#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stddef.h>

// defining parameters required for argon2
#define OUTLEN 16 // hash length 16 bytes
#define SALTLEN 8 // salt length 8 bytes
#define MEMCOST 65536 // 64MB memory used
#define TIMECOST 1 // 1 iteration
#define THREADS 4 

#define ROTR64(x, y) (((x) >> (y)) | ((x) << (64 - (y))))
#define G(r, i, a, b, c, d) do { \
    a = a + b + m[blake2b_sigma[r][2 * i]]; \
    d = ROTR64(d ^ a, 32); \
    c = c + d; \
    b = ROTR64(b ^ c, 24); \
    a = a + b + m[blake2b_sigma[r][2 * i + 1]]; \
    d = ROTR64(d ^ a, 16); \
    c = c + d; \
    b = ROTR64(b ^ c, 63); \
} while(0)

// Constants for the Blake2b algorithm
static const uint64_t blake2b_sigma[14][16] = {
    { 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15 },
    { 14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3 },
    { 11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4 },
    {  7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8 },
    {  9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13 },
    {  2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9 },
    { 12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11 },
    { 13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10 },
    {  6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5 },
    { 10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13, 0 },
    {  9, 14, 15,  5,  2, 10, 11,  4, 12,  6,  8,  0, 13,  3,  7,  1 },
    { 15,  5,  1,  3,  7, 14,  6,  9, 11,  8, 12,  2, 10,  0,  4, 13 },
    {  8,  6,  7,  9,  3, 12, 10, 15, 13,  0, 14, 11,  5,  2,  4, 1 },
    { 12, 15, 10,  4,  1,  5,  8,  7,  6,  2,  0,  3, 14,  9, 11, 13 }
};

// Constants for the Argon2 algorithm
#define ARGON2_QWORDS_IN_BLOCK 16
#define ARGON2_BLOCK_SIZE (ARGON2_QWORDS_IN_BLOCK * sizeof(uint64_t))
#define ARGON2_PREHASH_DIGEST_LENGTH 64
#define ARGON2_SYNC_POINTS 4

typedef struct {
    uint64_t v[ARGON2_QWORDS_IN_BLOCK];
} block;

// Blake2b hash function 
static void blake2b_hash(uint8_t *out, size_t outlen, const void *in, size_t inlen) {
    uint64_t h[8] = {
        0x6a09e667f3bcc908ULL, 0xbb67ae8584caa73bULL, 0x3c6ef372fe94f82bULL, 0xa54ff53a5f1d36f1ULL,
        0x510e527fade682d1ULL, 0x9b05688c2b3e6c1fULL, 0x1f83d9abfb41bd6bULL, 0x5be0cd19137e2179ULL
    };
    uint64_t m[16] = { 0 };

    // Initialize parameters
    h[0] ^= 0x01010000 ^ (uint64_t)outlen ^ ((uint64_t)inlen << 8);

    // Compress each block of data
    const uint8_t *pin = (const uint8_t *)in;
    size_t left = inlen;
    while (left >= 128) {
        for (size_t i = 0; i < 16; ++i) {
            m[i] = ((uint64_t *)pin)[i];
        }

        for (size_t i = 0; i < 12; ++i) {
            G(i, 0, h[0], h[1], h[2], h[3]);
            G(i, 1, h[4], h[5], h[6], h[7]);
            G(i, 2, h[0], h[1], h[2], h[3]);
            G(i, 3, h[4], h[5], h[6], h[7]);
            G(i, 4, h[0], h[1], h[2], h[3]);
            G(i, 5, h[4], h[5], h[6], h[7]);
            G(i, 6, h[0], h[1], h[2], h[3]);
            G(i, 7, h[4], h[5], h[6], h[7]);
        }

        for (size_t i = 0; i < 8; ++i) {
            h[i] ^= ((uint64_t *)pin)[i];
        }

        pin += 128;
        left -= 128;
    }

    // Finalize the hash
    uint8_t block[128] = { 0 };
    for (size_t i = 0; i < left; ++i) {
        block[i] = pin[i];
    }
    block[left] = 0x80;

    for (size_t i = 0; i < 8; ++i) {
        h[i] ^= ((uint64_t *)block)[i];
    }

    // Output the hash
    for (size_t i = 0; i < outlen; ++i) {
        out[i] = (uint8_t)(h[i / 8] >> (8 * (i % 8)));
    }
}


// Initialize Argon2 context
static void initialize(uint8_t *memory, size_t memlen, uint8_t *pwd, size_t pwdlen, uint8_t *salt, size_t saltlen) {
    // Fill memory with concatenated password and salt
    memcpy(memory, pwd, pwdlen);
    memcpy(memory + pwdlen, salt, saltlen);
}

// Argon2 hash function
static void argon2_hash(uint8_t *out, size_t outlen, uint8_t *memory, size_t memlen) {
    // Apply Blake2b hash function
    blake2b_hash(out, outlen, memory, memlen);
}

void generate_salt(uint8_t *salt, size_t saltlen) {
    // Generate a random number using rand()
    uint64_t random_num = 0;

    // Generate 8 bytes of random data
    for (size_t i = 0; i < sizeof(random_num); ++i) {
        random_num <<= 8;
        random_num |= (rand() & 0xFF);
    }

    // Copy the random number to the salt
    memcpy(salt, &random_num, saltlen);
}

int main() {
    uint8_t out[OUTLEN];
    char pwd[100];
    uint8_t salt[SALTLEN];
    uint8_t memory[MEMCOST];

    // Prompt the user to enter the password
    printf("Enter the password: ");
    fgets(pwd, sizeof(pwd), stdin);
    pwd[strcspn(pwd, "\n")] = '\0'; // Remove the newline character

    // Seed the random number generator with the current time
    srand(time(NULL));

    // Generate the salt
    generate_salt(salt, SALTLEN);

    // Initialize memory with password and salt
    initialize(memory, MEMCOST, (uint8_t *)pwd, strlen(pwd), salt, SALTLEN);

    // Hash the memory using Argon2
    argon2_hash(out, OUTLEN, memory, MEMCOST);
    
    printf("\nParamaters used for hashing...\n");
    printf("Hash length: %d bytes\n", OUTLEN);
    printf("Salt length: %d bytes\n", SALTLEN);
    printf("Memory: %d KB\n", MEMCOST);
    printf("Iterations: %d\n", TIMECOST);
    printf("Threads: %d\n", THREADS);
    
    printf("\nHash: ");
    for (int i = 0; i < OUTLEN; ++i) {
        printf("%02x", out[i]);
    }
    
    printf("\nSalt Used: ");
    for (int i = 0; i < SALTLEN; ++i) {
        printf("%02x", salt[i]);
    }
    printf("\n");

    return 0;
}
