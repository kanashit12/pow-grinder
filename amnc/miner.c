#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <pthread.h>
#include <stdatomic.h>
#include <time.h>
#include <unistd.h>

static const uint64_t RC[24] = {
 0x0000000000000001ULL,0x0000000000008082ULL,0x800000000000808aULL,0x8000000080008000ULL,
 0x000000000000808bULL,0x0000000080000001ULL,0x8000000080008081ULL,0x8000000000008009ULL,
 0x000000000000008aULL,0x0000000000000088ULL,0x0000000080008009ULL,0x000000008000000aULL,
 0x000000008000808bULL,0x800000000000008bULL,0x8000000000008089ULL,0x8000000000008003ULL,
 0x8000000000008002ULL,0x8000000000000080ULL,0x000000000000800aULL,0x800000008000000aULL,
 0x8000000080008081ULL,0x8000000000008080ULL,0x0000000080000001ULL,0x8000000080008008ULL};
static const int RHO[25] = {0,1,62,28,27, 36,44,6,55,20, 3,10,43,25,39, 41,45,15,21,8, 18,2,61,56,14};
static const int PI[25] = {0,6,12,18,24, 3,9,15,21,2, 1,7,13,19,20, 4,10,16,22,1+4, 5,11,17,23,4};
// pi index mapping: B[i] where i computed properly below; we use explicit permutation in round

static inline uint64_t rol(uint64_t x, int n){ return n==0?x:((x<<n)|(x>>(64-n))); }

static void keccakf(uint64_t st[25]){
  for(int round=0; round<24; round++){
    uint64_t C[5], D[5], B[25];
    for(int x=0;x<5;x++) C[x]=st[x]^st[x+5]^st[x+10]^st[x+15]^st[x+20];
    for(int x=0;x<5;x++) D[x]=C[(x+4)%5]^rol(C[(x+1)%5],1);
    for(int i=0;i<25;i++) st[i]^=D[i%5];
    // rho + pi: B[y + 5*((2x+3y)%5)] = rol(A[x+5y], R[x+5y]) with R indexed [x][y] table flattened x+5*y as RHO above? 
    // RHO here is stored as r[x+5*y] using table rows y: r[x][y] matrix given transposed; we use r_by_xy[x][y]:
    static const int r_by_xy[5][5] = {{0,36,3,41,18},{1,44,10,45,2},{62,6,43,15,61},{28,55,25,21,56},{27,20,39,8,14}};
    for(int x=0;x<5;x++) for(int y=0;y<5;y++){
      B[y + 5*((2*x+3*y)%5)] = rol(st[x+5*y], r_by_xy[x][y]);
    }
    // chi
    for(int y=0;y<5;y++) for(int x=0;x<5;x++){
      st[x+5*y] = B[x+5*y] ^ ((~B[(x+1)%5+5*y]) & B[(x+2)%5+5*y]);
    }
    st[0] ^= RC[round];
  }
}
// ---- AMNC specialized grinder ----
// preimage = abi.encode(seed32, wallet, agentId, lane, day, nonce) = 192 bytes.
// Block 1 (bytes 0..135) and the constant part of block 2 are folded into a
// precomputed state; per hash only the 4 nonce lanes change -> 1 permutation/hash.
static uint64_t BASE[25];
static uint64_t TGT[4]; // target as little-endian 64-bit words, TGT[3] = most significant
static atomic_int found_count;
static atomic_ullong total_tried;
static int want_count;
static FILE* outf;

static void u256_to_words_le(const uint8_t b[32], uint64_t w[4]){
  // b is big-endian 32 bytes; w[0] = least significant
  for(int i=0;i<4;i++){ uint64_t x=0; for(int j=0;j<8;j++) x |= (uint64_t)b[31-(i*8+j)] << (8*j); w[i]=x; }
}
static void setup_base(const uint8_t pre[192], const uint8_t target_be[32]){
  uint64_t st[25]={0};
  for(int i=0;i<17;i++){ uint64_t w=0; for(int j=0;j<8;j++) w |= (uint64_t)pre[i*8+j] << (8*j); st[i]=w; }
  keccakf(st);
  // block 2 constant part: bytes 136..159 (day remainder) go to lanes 0..2;
  // suffix 0x01 at block2 byte 56 -> lane 7 byte 0; final bit -> lane 16 byte 7.
  for(int i=0;i<3;i++){ uint64_t w=0; for(int j=0;j<8;j++) w |= (uint64_t)pre[136+i*8+j] << (8*j); st[i]^=w; }
  st[7] ^= 0x01ULL;
  st[16] ^= 0x8000000000000000ULL;
  memcpy(BASE, st, sizeof(BASE));
  u256_to_words_le(target_be, TGT);
}
static inline int digest_le_target(const uint64_t st[25]){
  // digest words: lane i little-endian value = uint256 byte-reversed segment; compare numeric:
  // numeric digest = sum lane_i * 2^(64*(3-i))? No: digest bytes out[0..31] = lanes 0..3 LE bytes.
  // uint256 value = out[0]*2^248 + ... ; most significant word = bytes 0..7 reversed = lane0 byte-reversed.
  uint64_t dw[4];
  for(int i=0;i<4;i++){ uint64_t x=st[i]; dw[3-i] = __builtin_bswap64(x); }
  // dw[3] now least significant? Careful: out bytes 0..7 = lane0 LE -> those are the TOP bytes of uint256.
  // top word (bytes 0..7 as BE) = bswap64(lane0). numeric compare from top word down:
  uint64_t top[4]; top[0]=__builtin_bswap64(st[0]); top[1]=__builtin_bswap64(st[1]); top[2]=__builtin_bswap64(st[2]); top[3]=__builtin_bswap64(st[3]);
  uint64_t tt[4]; // target top-down: TGT[3] is most significant word already in numeric form
  tt[0]=TGT[3]; tt[1]=TGT[2]; tt[2]=TGT[1]; tt[3]=TGT[0];
  for(int i=0;i<4;i++){ if(top[i]<tt[i]) return 1; if(top[i]>tt[i]) return 0; }
  (void)dw; return 1; // equal counts as <= target
}
typedef struct { int id; int stride; } warg;
static void* worker(void* p){
  warg* a=(warg*)p;
  uint64_t st[25];
  uint64_t counter = (uint64_t)a->id;
  uint64_t local=0;
  while(atomic_load(&found_count) < want_count){
    memcpy(st, BASE, sizeof(st));
    // nonce = counter in low 64 bits -> nonce word bytes 24..31 (BE) = counter BE.
    // nonce lanes (block2 lanes 3..6) hold preimage bytes 160..191 little-endian per lane:
    // lane3 = bytes160..167 = nonce bytes 0..7 = 0 (counter < 2^64)
    // lane4 = bytes168..175 = nonce bytes 8..15 = 0
    // lane5 = bytes176..183 = nonce bytes 16..23 = 0
    // lane6 = bytes184..191 = nonce bytes 24..31: LE lane = reverse of BE counter bytes
    st[6] ^= __builtin_bswap64(counter);
    keccakf(st);
    local++;
    if(digest_le_target(st)){
      int n = atomic_fetch_add(&found_count, 1) + 1;
      fprintf(outf, "FOUND %llu\n", (unsigned long long)counter); fflush(outf);
      printf("FOUND %llu (%d/%d)\n", (unsigned long long)counter, n, want_count); fflush(stdout);
    }
    counter += a->stride;
    if((local & 0xFFFF)==0){ atomic_fetch_add(&total_tried, local); local=0; }
  }
  atomic_fetch_add(&total_tried, local);
  return NULL;
}

static void dec_to_bytes32(const char* s, uint8_t out[32]){
  memset(out, 0, 32);
  while(*s){ int carry = *s - '0'; for(int i=31;i>=0;i--){ int v = out[i]*10 + carry; out[i]=(uint8_t)(v & 0xFF); carry = v >> 8; } s++; }
}
static int hexval2(char c){ if(c>='0'&&c<='9') return c-'0'; if(c>='a'&&c<='f') return c-'a'+10; if(c>='A'&&c<='F') return c-'A'+10; return 0; }
static void parse_hex(const char* s, uint8_t* out, int nbytes){
  if(s[0]=='0'&&(s[1]=='x'||s[1]=='X')) s+=2;
  int len = (int)strlen(s); int start = len - 2*nbytes; // right-align: short strings get leading zero nibbles
  for(int i=0;i<nbytes;i++){
    int hi_idx = start + 2*i, lo_idx = hi_idx + 1;
    int hi = hi_idx >= 0 && hi_idx < len ? hexval2(s[hi_idx]) : 0;
    int lo = lo_idx >= 0 && lo_idx < len ? hexval2(s[lo_idx]) : 0;
    out[i]=(uint8_t)(hi*16+lo);
  }
}
int main(int argc, char** argv){
  if(argc>=2 && strcmp(argv[1],"--digest")==0){
    // --digest seed wallet agentId lane day nonce  -> print digest hex (validation mode)
    uint8_t pre[192]={0}; uint8_t seed[32]; parse_hex(argv[2], seed, 32); memcpy(pre, seed, 32);
    uint8_t wal[20]; parse_hex(argv[3], wal, 20); memcpy(pre+44, wal, 20);
    dec_to_bytes32(argv[4], pre+64);
    uint64_t lane=strtoull(argv[5],NULL,10), day=strtoull(argv[6],NULL,10), nonce=strtoull(argv[7],NULL,10);
    for(int i=0;i<8;i++){ pre[96+31-i]=(uint8_t)(lane>>(8*i)); pre[128+31-i]=(uint8_t)(day>>(8*i)); pre[160+31-i]=(uint8_t)(nonce>>(8*i)); }
    uint64_t st[25]={0};
    for(int i=0;i<17;i++){ uint64_t w=0; for(int j=0;j<8;j++) w|=(uint64_t)pre[i*8+j]<<(8*j); st[i]=w; }
    keccakf(st);
    uint8_t blk2[56]; memcpy(blk2, pre+136, 56);
    for(int i=0;i<7;i++){ uint64_t w=0; for(int j=0;j<8;j++) w|=(uint64_t)blk2[i*8+j]<<(8*j); st[i]^=w; }
    st[7]^=0x01ULL; st[16]^=0x8000000000000000ULL; keccakf(st);
    printf("0x"); for(int i=0;i<4;i++){ uint64_t w=st[i]; for(int j=0;j<8;j++) printf("%02x",(uint8_t)(w>>(8*j))); } printf("\n");
    return 0;
  }
  if(argc<10){ fprintf(stderr,"usage: miner seed_hex wallet_hex agentId_dec lane day target_hex want threads outfile\n"); return 2; }
  uint8_t pre[192]={0}; uint8_t seed[32]; parse_hex(argv[1], seed, 32); memcpy(pre, seed, 32);
  uint8_t wal[20]; parse_hex(argv[2], wal, 20); memcpy(pre+44, wal, 20);
  dec_to_bytes32(argv[3], pre+64);
  uint64_t lane=strtoull(argv[4],NULL,10), day=strtoull(argv[5],NULL,10);
  for(int i=0;i<8;i++){ pre[96+31-i]=(uint8_t)(lane>>(8*i)); pre[128+31-i]=(uint8_t)(day>>(8*i)); }
  uint8_t tgt[32]; parse_hex(argv[6], tgt, 32);
  want_count = atoi(argv[7]); int T = atoi(argv[8]);
  outf = fopen(argv[9], "a"); if(!outf){ perror("outfile"); return 2; }
  setup_base(pre, tgt);
  pthread_t th[16]; warg args[16];
  struct timespec t0,t1; clock_gettime(CLOCK_MONOTONIC,&t0);
  for(int i=0;i<T;i++){ args[i].id=i; args[i].stride=T; pthread_create(&th[i],NULL,worker,&args[i]); }
  for(int i=0;i<T;i++) pthread_join(th[i],NULL);
  clock_gettime(CLOCK_MONOTONIC,&t1);
  double dt=(t1.tv_sec-t0.tv_sec)+(t1.tv_nsec-t0.tv_nsec)/1e9;
  printf("DONE found=%d tried=%llu elapsed=%.1fs rate=%.0f H/s\n", atomic_load(&found_count),
         (unsigned long long)atomic_load(&total_tried), dt, atomic_load(&total_tried)/dt);
  fclose(outf);
  return 0;
}
