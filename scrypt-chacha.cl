/*
	scrypt-jane by Andrew M, https://github.com/floodyberry/scrypt-jane

	Public Domain or MIT License, whichever is easier
*/

#define SCRYPT_HASH "Keccak-512"
#define SCRYPT_HASH_DIGEST_SIZE 64
#define SCRYPT_KECCAK_F 1600
#define SCRYPT_HASH_BLOCK_SIZE 72
#define SCRYPT_BLOCK_BYTES 64
#define SCRYPT_BLOCK_WORDS 16
#define ROTL64(x, y) rotate(x, y)
#define ROTL32(x, y) rotate(x, y)

typedef struct scrypt_hash_state_t {
	ulong state[SCRYPT_KECCAK_F / 64];
	ulong leftover;
        uint buffer[SCRYPT_HASH_BLOCK_SIZE / 4];
} scrypt_hash_state;

typedef struct scrypt_hmac_state_t {
	scrypt_hash_state inner;
	scrypt_hash_state outer;
} scrypt_hmac_state;


__constant ulong keccak_round_constants[24] = {
	0x0000000000000001UL, 0x0000000000008082UL,
	0x800000000000808aUL, 0x8000000080008000UL,
	0x000000000000808bUL, 0x0000000080000001UL,
	0x8000000080008081UL, 0x8000000000008009UL,
	0x000000000000008aUL, 0x0000000000000088UL,
	0x0000000080008009UL, 0x000000008000000aUL,
	0x000000008000808bUL, 0x800000000000008bUL,
	0x8000000000008089UL, 0x8000000000008003UL,
	0x8000000000008002UL, 0x8000000000000080UL,
	0x000000000000800aUL, 0x800000008000000aUL,
	0x8000000080008081UL, 0x8000000000008080UL,
	0x0000000080000001UL, 0x8000000080008008UL
};


static void
keccak_block(scrypt_hash_state *S, const ulong *in) {
        ulong t[5];
        ulong u[5];
        ulong v;
        ulong w;
        ulong *s = S->state;
        uint i;

	/* absorb input */
        s[0] ^= in[0];
        s[1] ^= in[1];
        s[2] ^= in[2];
        s[3] ^= in[3];
        s[4] ^= in[4];
        s[5] ^= in[5];
        s[6] ^= in[6];
        s[7] ^= in[7];
        s[8] ^= in[8];
	
	for (i = 0; i < 24; i++) {
		/* theta: c = a[0,i] ^ a[1,i] ^ .. a[4,i] */
		t[0] = s[0] ^ s[5] ^ s[10] ^ s[15] ^ s[20];
		t[1] = s[1] ^ s[6] ^ s[11] ^ s[16] ^ s[21];
		t[2] = s[2] ^ s[7] ^ s[12] ^ s[17] ^ s[22];
		t[3] = s[3] ^ s[8] ^ s[13] ^ s[18] ^ s[23];
		t[4] = s[4] ^ s[9] ^ s[14] ^ s[19] ^ s[24];
            
		/* theta: d[i] = c[i+4] ^ rotl(c[i+1],1) */
		u[0] = t[4] ^ ROTL64(t[1], 1UL);
		u[1] = t[0] ^ ROTL64(t[2], 1UL);
		u[2] = t[1] ^ ROTL64(t[3], 1UL);
		u[3] = t[2] ^ ROTL64(t[4], 1UL);
		u[4] = t[3] ^ ROTL64(t[0], 1UL);

		/* theta: a[0,i], a[1,i], .. a[4,i] ^= d[i] */
		s[0] ^= u[0]; s[5] ^= u[0]; s[10] ^= u[0]; s[15] ^= u[0]; s[20] ^= u[0];
		s[1] ^= u[1]; s[6] ^= u[1]; s[11] ^= u[1]; s[16] ^= u[1]; s[21] ^= u[1];
		s[2] ^= u[2]; s[7] ^= u[2]; s[12] ^= u[2]; s[17] ^= u[2]; s[22] ^= u[2];
		s[3] ^= u[3]; s[8] ^= u[3]; s[13] ^= u[3]; s[18] ^= u[3]; s[23] ^= u[3];
		s[4] ^= u[4]; s[9] ^= u[4]; s[14] ^= u[4]; s[19] ^= u[4]; s[24] ^= u[4];

		/* rho pi: b[..] = rotl(a[..], ..) */
		v = s[ 1];
		s[ 1] = ROTL64(s[ 6], 44UL);
		s[ 6] = ROTL64(s[ 9], 20UL);
		s[ 9] = ROTL64(s[22], 61UL);
		s[22] = ROTL64(s[14], 39UL);
		s[14] = ROTL64(s[20], 18UL);
		s[20] = ROTL64(s[ 2], 62UL);
		s[ 2] = ROTL64(s[12], 43UL);
		s[12] = ROTL64(s[13], 25UL);
		s[13] = ROTL64(s[19],  8UL);
		s[19] = ROTL64(s[23], 56UL);
		s[23] = ROTL64(s[15], 41UL);
		s[15] = ROTL64(s[ 4], 27UL);
		s[ 4] = ROTL64(s[24], 14UL);
		s[24] = ROTL64(s[21],  2UL);
		s[21] = ROTL64(s[ 8], 55UL);
		s[ 8] = ROTL64(s[16], 45UL);
		s[16] = ROTL64(s[ 5], 36UL);
		s[ 5] = ROTL64(s[ 3], 28UL);
		s[ 3] = ROTL64(s[18], 21UL);
		s[18] = ROTL64(s[17], 15UL);
		s[17] = ROTL64(s[11], 10UL);
		s[11] = ROTL64(s[ 7],  6UL);
		s[ 7] = ROTL64(s[10],  3UL);
		s[10] = ROTL64(    v,  1UL);

		/* chi: a[i,j] ^= ~b[i,j+1] & b[i,j+2] */
		v = s[ 0]; w = s[ 1]; s[ 0] ^= (~w) & s[ 2]; s[ 1] ^= (~s[ 2]) & s[ 3]; s[ 2] ^= (~s[ 3]) & s[ 4]; s[ 3] ^= (~s[ 4]) & v; s[ 4] ^= (~v) & w;
		v = s[ 5]; w = s[ 6]; s[ 5] ^= (~w) & s[ 7]; s[ 6] ^= (~s[ 7]) & s[ 8]; s[ 7] ^= (~s[ 8]) & s[ 9]; s[ 8] ^= (~s[ 9]) & v; s[ 9] ^= (~v) & w;
		v = s[10]; w = s[11]; s[10] ^= (~w) & s[12]; s[11] ^= (~s[12]) & s[13]; s[12] ^= (~s[13]) & s[14]; s[13] ^= (~s[14]) & v; s[14] ^= (~v) & w;
		v = s[15]; w = s[16]; s[15] ^= (~w) & s[17]; s[16] ^= (~s[17]) & s[18]; s[17] ^= (~s[18]) & s[19]; s[18] ^= (~s[19]) & v; s[19] ^= (~v) & w;
		v = s[20]; w = s[21]; s[20] ^= (~w) & s[22]; s[21] ^= (~s[22]) & s[23]; s[22] ^= (~s[23]) & s[24]; s[23] ^= (~s[24]) & v; s[24] ^= (~v) & w;

		/* iota: a[0,0] ^= round constant */
		s[0] ^= keccak_round_constants[i];
	}
}

__constant uint4 ZERO = (uint4)(0);
__constant uint2 ZERO_UINT2 = (uint2)(0);
__constant ulong2 ZERO_ULONG = (ulong2)(0);

static void
scrypt_hash_init(scrypt_hash_state *S) {
        vstore2(ZERO_ULONG, 0, S->state);
        vstore2(ZERO_ULONG, 1, S->state);
        vstore2(ZERO_ULONG, 2, S->state);
        vstore2(ZERO_ULONG, 3, S->state);
        vstore2(ZERO_ULONG, 4, S->state);
        vstore2(ZERO_ULONG, 5, S->state);
        vstore2(ZERO_ULONG, 6, S->state);
        vstore2(ZERO_ULONG, 7, S->state);
        vstore2(ZERO_ULONG, 8, S->state);
        vstore2(ZERO_ULONG, 9, S->state);
        vstore2(ZERO_ULONG, 10, S->state);
        vstore2(ZERO_ULONG, 11, S->state);
        S->state[24] = 0;
	S->leftover = 0;
        vstore4(ZERO, 0, S->buffer);
        vstore4(ZERO, 1, S->buffer);
        vstore4(ZERO, 2, S->buffer);
        vstore4(ZERO, 3, S->buffer);
        vstore2(ZERO_UINT2, 8, S->buffer);
}

static void
scrypt_hash_update_72(scrypt_hash_state *S, uchar *in) {
	/* handle the current data */
        keccak_block(S, (ulong *)in);
}

static void
scrypt_hash_update_80(scrypt_hash_state *S, uchar *in) {
	/* handle the current data */
	keccak_block(S, (ulong *)in);
	in += SCRYPT_HASH_BLOCK_SIZE;

	/* handle leftover data */
	S->leftover = 2;
        S->buffer[0] = ((uint *)in)[0];
        S->buffer[1] = ((uint *)in)[1];
}

static void
scrypt_hash_update_128(scrypt_hash_state *S, uchar *in) {
	/* handle the current data */
	keccak_block(S, (ulong *)in);
	in += SCRYPT_HASH_BLOCK_SIZE;

	/* handle leftover data */
	S->leftover = 14;
        S->buffer[0] = ((uint *)in)[0];
        S->buffer[1] = ((uint *)in)[1];
        S->buffer[2] = ((uint *)in)[2];
        S->buffer[3] = ((uint *)in)[3];
        S->buffer[4] = ((uint *)in)[4];
        S->buffer[5] = ((uint *)in)[5];
        S->buffer[6] = ((uint *)in)[6];
        S->buffer[7] = ((uint *)in)[7];
        S->buffer[8] = ((uint *)in)[8];
        S->buffer[9] = ((uint *)in)[9];
        S->buffer[10] = ((uint *)in)[10];
        S->buffer[11] = ((uint *)in)[11];
        S->buffer[12] = ((uint *)in)[12];
        S->buffer[13] = ((uint *)in)[13];
}

static void
scrypt_hash_update_4(scrypt_hash_state *S, uint in) {
	/* handle the previous data */
        S->buffer[S->leftover] = in;
	S->leftover += 1;
}

static void
scrypt_hash_update_64(scrypt_hash_state *S, uchar *in) {
	/* handle leftover data */
	S->leftover = 16;
        S->buffer[0] = ((uint *)in)[0];
        S->buffer[1] = ((uint *)in)[1];
        S->buffer[2] = ((uint *)in)[2];
        S->buffer[3] = ((uint *)in)[3];
        S->buffer[4] = ((uint *)in)[4];
        S->buffer[5] = ((uint *)in)[5];
        S->buffer[6] = ((uint *)in)[6];
        S->buffer[7] = ((uint *)in)[7];
        S->buffer[8] = ((uint *)in)[8];
        S->buffer[9] = ((uint *)in)[9];
        S->buffer[10] = ((uint *)in)[10];
        S->buffer[11] = ((uint *)in)[11];
        S->buffer[12] = ((uint *)in)[12];
        S->buffer[13] = ((uint *)in)[13];
        S->buffer[14] = ((uint *)in)[14];
        S->buffer[15] = ((uint *)in)[15];
}

static void
scrypt_hash_finish_80(scrypt_hash_state *S, ulong *hash) {
	S->buffer[S->leftover] = 0x01;
	S->buffer[17] = 0x80000000;
    
	keccak_block(S, (ulong *)S->buffer);

        hash[0] = S->state[0];
        hash[1] = S->state[1];
        hash[2] = S->state[2];
        hash[3] = S->state[3];
        hash[4] = S->state[4];
        hash[5] = S->state[5];
        hash[6] = S->state[6];
        hash[7] = S->state[7];
}

static void
scrypt_hash_80(ulong *hash, uchar *m) {
	scrypt_hash_state st;
	scrypt_hash_init(&st);
	scrypt_hash_update_80(&st, m);
	scrypt_hash_finish_80(&st, hash);
}

/* hmac */
__constant uint2 KEY_0X36 = (uint2)(0x36363636);
__constant uint2 KEY_0X36_XOR_0X5C = (uint2)(0x6A6A6A6A);

static void
scrypt_hmac_init(scrypt_hmac_state *st, uchar *key) {
        uint2 pad[SCRYPT_HASH_BLOCK_SIZE/8];
        
	scrypt_hash_init(&st->inner);
	scrypt_hash_init(&st->outer);

	/* if it's > blocksize bytes, hash it */
	scrypt_hash_80((ulong *)pad, key);
        pad[8] = 0;

	/* inner = (key ^ 0x36) */
	/* h(inner || ...) */
        pad[0] ^= KEY_0X36;
        pad[1] ^= KEY_0X36;
        pad[2] ^= KEY_0X36;
        pad[3] ^= KEY_0X36;
        pad[4] ^= KEY_0X36;
        pad[5] ^= KEY_0X36;
        pad[6] ^= KEY_0X36;
        pad[7] ^= KEY_0X36;
        pad[8] ^= KEY_0X36;
	scrypt_hash_update_72(&st->inner, (uchar *)pad);

	/* outer = (key ^ 0x5c) */
	/* h(outer || ...) */
        pad[0] ^= KEY_0X36_XOR_0X5C;
        pad[1] ^= KEY_0X36_XOR_0X5C;
        pad[2] ^= KEY_0X36_XOR_0X5C;
        pad[3] ^= KEY_0X36_XOR_0X5C;
        pad[4] ^= KEY_0X36_XOR_0X5C;
        pad[5] ^= KEY_0X36_XOR_0X5C;
        pad[6] ^= KEY_0X36_XOR_0X5C;
        pad[7] ^= KEY_0X36_XOR_0X5C;
        pad[8] ^= KEY_0X36_XOR_0X5C;
	scrypt_hash_update_72(&st->outer, (uchar *)pad);
}

static void
scrypt_hmac_update_80(scrypt_hmac_state *st, uchar *m) {
	/* h(inner || m...) */
	scrypt_hash_update_80(&st->inner, m);
}

static void
scrypt_hmac_update_128(scrypt_hmac_state *st, uchar *m) {
	/* h(inner || m...) */
	scrypt_hash_update_128(&st->inner, m);
}

static void
scrypt_hmac_update_4(scrypt_hmac_state *st, uint m) {
	/* h(inner || m...) */
	scrypt_hash_update_4(&st->inner, m);
}

static void
scrypt_hmac_finish(scrypt_hmac_state *st, ulong *mac) {
	/* h(inner || m) */
	ulong innerhash[8];
	scrypt_hash_finish_80(&st->inner, innerhash);

	/* h(outer || h(inner || m)) */
	scrypt_hash_update_64(&st->outer, (uchar *)innerhash);
	scrypt_hash_finish_80(&st->outer, (ulong *)mac);
}

__constant uint be1 = 0x01000000;
__constant uint be2 = 0x02000000;

static void
scrypt_pbkdf2_128B(uchar *password, uint password_len, uchar *salt, uint salt_len, ulong *out) {
	scrypt_hmac_state hmac_pw, work;
	ulong ti[8];
        
	/* bytes must be <= (0xffffffff - (SCRYPT_HASH_DIGEST_SIZE - 1)), which they will always be under scrypt */

	/* hmac(password, ...) */
	scrypt_hmac_init(&hmac_pw, password);

	/* hmac(password, salt...) */
	scrypt_hmac_update_80(&hmac_pw, salt);

        	/* U1 = hmac(password, salt || be(i)) */
		/* U32TO8_BE(be, i); */
		work = hmac_pw;
		scrypt_hmac_update_4(&work, be1);
		scrypt_hmac_finish(&work, ti);

                vstore2(((ulong2 *)ti)[0], 0, out);
                vstore2(((ulong2 *)ti)[1], 1, out);
                vstore2(((ulong2 *)ti)[2], 2, out);
                vstore2(((ulong2 *)ti)[3], 3, out);
                
                /* U1 = hmac(password, salt || be(i)) */
		/* U32TO8_BE(be, i); */
		// work = hmac_pw;
		scrypt_hmac_update_4(&hmac_pw, be2);
		scrypt_hmac_finish(&hmac_pw, ti);

                vstore2(((ulong2 *)ti)[0], 4, out);
                vstore2(((ulong2 *)ti)[1], 5, out);
                vstore2(((ulong2 *)ti)[2], 6, out);
                vstore2(((ulong2 *)ti)[3], 7, out);
}

static void
scrypt_pbkdf2_32B(uchar *password, uint password_len, uchar *salt, uint salt_len, ulong *out) {
	scrypt_hmac_state hmac_pw;
	ulong ti[8];
	
	/* bytes must be <= (0xffffffff - (SCRYPT_HASH_DIGEST_SIZE - 1)), which they will always be under scrypt */

	/* hmac(password, ...) */
	scrypt_hmac_init(&hmac_pw, password);

	/* hmac(password, salt...) */
	scrypt_hmac_update_128(&hmac_pw, salt);

		/* U1 = hmac(password, salt || be(i)) */
		/* U32TO8_BE(be, i); */
		scrypt_hmac_update_4(&hmac_pw, be1);
		scrypt_hmac_finish(&hmac_pw, ti);

                out[0] = ti[0];
                out[1] = ti[1];
                out[2] = ti[2];
                out[3] = ti[3];
}

__constant uint4 MASK_2 = (uint4) (1, 2, 3, 0);
__constant uint4 MASK_3 = (uint4) (2, 3, 0, 1);
__constant uint4 MASK_4 = (uint4) (3, 0, 1, 2);
__constant uint4 ROTATE_16 = (uint4) (16, 16, 16, 16);
__constant uint4 ROTATE_12 = (uint4) (12, 12, 12, 12);
__constant uint4 ROTATE_8 = (uint4) (8, 8, 8, 8);
__constant uint4 ROTATE_7 = (uint4) (7, 7, 7, 7);

static void
chacha_core(uint4 state[4]) {
	uint4 x[4];
        uint4 t;
	uint rounds;

	x[0] = state[0];
	x[1] = state[1];
	x[2] = state[2];
	x[3] = state[3];

        #pragma unroll
	for (rounds = 0; rounds < 4; rounds ++) {
                x[0] += x[1]; t = x[3] ^ x[0]; x[3] = ROTL32(t, ROTATE_16);
                x[2] += x[3]; t = x[1] ^ x[2]; x[1] = ROTL32(t, ROTATE_12);
                x[0] += x[1]; t = x[3] ^ x[0]; x[3] = ROTL32(t, ROTATE_8);
                x[2] += x[3]; t = x[1] ^ x[2]; x[1] = ROTL32(t, ROTATE_7);
                
                // x[1] = shuffle(x[1], MASK_2);
                // x[2] = shuffle(x[2], MASK_3);
                // x[3] = shuffle(x[3], MASK_4);
                
                x[0]      += x[1].yzwx; t = x[3].wxyz ^ x[0];      x[3].wxyz = ROTL32(t, ROTATE_16);
                x[2].zwxy += x[3].wxyz; t = x[1].yzwx ^ x[2].zwxy; x[1].yzwx = ROTL32(t, ROTATE_12);
                x[0]      += x[1].yzwx; t = x[3].wxyz ^ x[0];      x[3].wxyz = ROTL32(t, ROTATE_8);
                x[2].zwxy += x[3].wxyz; t = x[1].yzwx ^ x[2].zwxy; x[1].yzwx = ROTL32(t, ROTATE_7);
                
                // x[1] = shuffle(x[1], MASK_4);
                // x[2] = shuffle(x[2], MASK_3);
                // x[3] = shuffle(x[3], MASK_2);
	}

	state[0] += x[0];
	state[1] += x[1];
	state[2] += x[2];
	state[3] += x[3];
}

static void
scrypt_ChunkMix_Bxor(uint4 *Bout/*[chunkWords]*/, uint4 *Bin/*[chunkWords]*/, __global uint4 *Bxor/*[chunkWords]*/) {
	/* 1: X = B_{2r - 1} */

	/* 2: for i = 0 to 2r - 1 do */
		/* 3: X = H(X ^ B_i) */
		Bout[0] = Bin[4] ^ Bxor[4] ^ Bin[0] ^ Bxor[0];
		Bout[1] = Bin[5] ^ Bxor[5] ^ Bin[1] ^ Bxor[1];
		Bout[2] = Bin[6] ^ Bxor[6] ^ Bin[2] ^ Bxor[2];
		Bout[3] = Bin[7] ^ Bxor[7] ^ Bin[3] ^ Bxor[3];
                
		/* SCRYPT_MIX_FN */ chacha_core(Bout);

		/* 4: Y_i = X */
		/* 6: B'[0..r-1] = Y_even */
		/* 6: B'[r..2r-1] = Y_odd */


		/* 3: X = H(X ^ B_i) */
		Bout[4] = Bout[0] ^ Bin[4] ^ Bxor[4];
		Bout[5] = Bout[1] ^ Bin[5] ^ Bxor[5];
		Bout[6] = Bout[2] ^ Bin[6] ^ Bxor[6];
		Bout[7] = Bout[3] ^ Bin[7] ^ Bxor[7];
                
		/* SCRYPT_MIX_FN */ chacha_core(Bout + 4);

		/* 4: Y_i = X */
		/* 6: B'[0..r-1] = Y_even */
		/* 6: B'[r..2r-1] = Y_odd */
}

static void
scrypt_ChunkMix(__global uint4 *Bout/*[chunkWords]*/, __global uint4 *Bin/*[chunkWords]*/) {
	uint4 X[4];

	/* 1: X = B_{2r - 1} */

	/* 2: for i = 0 to 2r - 1 do */
		/* 3: X = H(X ^ B_i) */
                X[0] = Bin[4] ^ Bin[0];
                X[1] = Bin[5] ^ Bin[1];
                X[2] = Bin[6] ^ Bin[2];
                X[3] = Bin[7] ^ Bin[3];

		/* SCRYPT_MIX_FN */ chacha_core(X);

		/* 4: Y_i = X */
		/* 6: B'[0..r-1] = Y_even */
		/* 6: B'[r..2r-1] = Y_odd */
                Bout[0] = X[0];
                Bout[1] = X[1];
                Bout[2] = X[2];
                Bout[3] = X[3];


		/* 3: X = H(X ^ B_i) */
		X[0] ^= Bin[4];
		X[1] ^= Bin[5];
		X[2] ^= Bin[6];
		X[3] ^= Bin[7];

		/* SCRYPT_MIX_FN */ chacha_core(X);

		/* 4: Y_i = X */
		/* 6: B'[0..r-1] = Y_even */
		/* 6: B'[r..2r-1] = Y_odd */
                Bout[4] = X[0];
                Bout[5] = X[1];
                Bout[6] = X[2];
                Bout[7] = X[3];
}

static void
scrypt_ChunkMix_local(uint4 *Bout/*[chunkWords]*/, __global uint4 *Bin/*[chunkWords]*/) {
	/* 1: X = B_{2r - 1} */

	/* 2: for i = 0 to 2r - 1 do */
		/* 3: X = H(X ^ B_i) */
                Bout[0] = Bin[4] ^ Bin[0];
                Bout[1] = Bin[5] ^ Bin[1];
                Bout[2] = Bin[6] ^ Bin[2];
                Bout[3] = Bin[7] ^ Bin[3];

		/* SCRYPT_MIX_FN */ chacha_core(Bout);

		/* 4: Y_i = X */
		/* 6: B'[0..r-1] = Y_even */
		/* 6: B'[r..2r-1] = Y_odd */


		/* 3: X = H(X ^ B_i) */
		Bout[4] = Bout[0] ^ Bin[4];
		Bout[5] = Bout[1] ^ Bin[5];
		Bout[6] = Bout[2] ^ Bin[6];
		Bout[7] = Bout[3] ^ Bin[7];

		/* SCRYPT_MIX_FN */ chacha_core(Bout + 4);

		/* 4: Y_i = X */
		/* 6: B'[0..r-1] = Y_even */
		/* 6: B'[r..2r-1] = Y_odd */
}

__constant uint chunkWords = 16 * 2;

static void
scrypt_ROMix(uint4 *X/*[chunkWords]*/, uint4 *Y/*[chunkWords]*/, __global uint4 *V/*[N * chunkWords]*/, uint N) {
	__global uint4 *block = V;
	uint i, j;

	/* 1: X = B */
	/* implicit */

	/* 2: for i = 0 to N - 1 do */
        block[0] = X[0];
        block[1] = X[1];
        block[2] = X[2];
        block[3] = X[3];
        block[4] = X[4];
        block[5] = X[5];
        block[6] = X[6];
        block[7] = X[7];
	for (i = 0; i < N - 1; i++, block += 8) {
		/* 3: V_i = X */
		/* 4: X = H(X) */
		scrypt_ChunkMix(block + 8, block);
	}
	scrypt_ChunkMix_local(X, block);

	/* 6: for i = 0 to N - 1 do */
	for (i = 0; i < N; i += 2) {
		/* 7: j = Integerify(X) % N */
		j = X[4].x & (N - 1);

		/* 8: X = H(Y ^ V_j) */
		scrypt_ChunkMix_Bxor(Y, X, V + j * 8);

		/* 7: j = Integerify(Y) % N */
		j = Y[4].x & (N - 1);

		/* 8: X = H(Y ^ V_j) */
		scrypt_ChunkMix_Bxor(X, Y, V + j * 8);
	}

	/* 10: B' = X */
	/* implicit */
}

__constant uint ES[2] = { 0x00FF00FF, 0xFF00FF00 };
#define FOUND (0xFF)
#define SETFOUND(Xnonce) output[output[FOUND]++] = Xnonce
#define EndianSwap(n) (rotate(n & ES[0], 24U)|rotate(n & ES[1], 8U))

__attribute__((reqd_work_group_size(WORKSIZE, 1, 1)))
__kernel void search(__global const uint4 * restrict input,
volatile __global uint * restrict output, __global uchar * restrict padcache,
const uint4 midstate0, const uint4 midstate16, const uint target, const uint nfactor)
{
        uint4 password[5];
        uint4 X[8];
        uint4 Y[8];
        uint output_hash[8];
	uint gid = get_global_id(0);
        uint goffset = get_global_offset(0);
        uint index = gid - goffset;
    	__global uchar *V;
        
        password[0] = input[0];
        password[1] = input[1];
        password[2] = input[2];
        password[3] = input[3];
        password[4] = input[4];
        password[4].w = gid;
        
	/* 1: X = PBKDF2(password, salt) */
        scrypt_pbkdf2_128B((uchar *)password, 80, (uchar *)password, 80, (ulong *)X);

	/* 2: X = ROMix(X) */
	V = padcache + index * (nfactor + 1) * SCRYPT_BLOCK_BYTES * 2;
        scrypt_ROMix(X, Y, (__global uint4 *)V, nfactor);

	/* 3: Out = PBKDF2(password, X) */
	scrypt_pbkdf2_32B((uchar *)password, 80, (uchar *)X, SCRYPT_BLOCK_BYTES * 2, (ulong *)output_hash);
        
        bool result = (output_hash[7] <= target);
        if (result)
            SETFOUND(gid);
}
