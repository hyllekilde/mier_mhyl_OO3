/* File ListC/listmachine.c
   A unified-stack abstract machine and garbage collector 
   for list-C, a variant of micro-C with cons cells.
   sestoft@itu.dk * 2009-11-17, 2012-02-08

   Compile like this, on ssh.itu.dk say:
   gcc -Wall listmachine.c -o listmachine

   If necessary, force compiler to use 32 bit integers:
   gcc -m32 -Wall listmachine.c -o listmachine

   To execute a program file using this abstract machine, do:
   ./listmachine <programfile> <arg1> <arg2> ...
   To get also a trace of the program execution:
   ./listmachine -trace <programfile> <arg1> <arg2> ...

   This code assumes -- and checks -- that values of type
   int, unsigned int and unsigned int* have size 32 bits.
   */

/*
   Data representation in the stack s[...] and the heap:
 * All integers are tagged with a 1 bit in the least significant
 position, regardless of whether they represent program integers,
 return addresses, array base addresses or old base pointers
 (into the stack).  
 * All heap references are word-aligned, that is, the two least
 significant bits of a heap reference are 00.  
 * Integer constants and code addresses in the program array
 p[...] are not tagged.
 The distinction between integers and references is necessary for 
 the garbage collector to be precise (not conservative).

 The heap consists of 32-bit words, and the heap is divided into 
 blocks.  A block has a one-word header block[0] followed by the 
 block's contents: zero or more words block[i], i=1..n.

 A header has the form ttttttttnnnnnnnnnnnnnnnnnnnnnngg
 where tttttttt is the block tag, all 0 for cons cells
 nn....nn is the block length (excluding header)
 gg       is the block's color

 The block color has this meaning:
 gg=00=White: block is dead (after mark, before sweep)
 gg=01=Grey:  block is live, children not marked (during mark)
 gg=11=Black: block is live (after mark, before sweep)
 gg=11=Blue:  block is on the freelist or orphaned

 A block of length zero is an orphan; it cannot be used 
 for data and cannot be on the freelist.  An orphan is 
 created when allocating all but the last word of a free block.
 */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <sys/time.h>
#include <sys/resource.h>

typedef unsigned int word; //A block, to be used for storing data (both header and concrete data)

//Integer tagging helper methods
#define IsInt(v) (((v)&1)==1) //Check if first bit is an 1 -> Then we have an integer
#define Tag(v) (((v)<<1)|1) //Shift all bits one left and set first bit to 1 (tag as integer)
#define Untag(v) ((v)>>1) //Shift all bits one right; remove tha tag (untag as integer)
#define IsReference(v) v!=0 && !IsInt(v) //If it's not Nil and not an Integer, it must be a refernce in list-c

//Color definitions
#define White 0 //Block is dead (after mark, before sweep)
#define Grey  1 //Block is live, children not marked (during mark)
#define Black 2 //Block is live (aftermark, before sweep)
#define Blue  3 //Block is on the freelist or orphaned

#define BlockTag(hdr) ((hdr)>>24) //Shift 24 bits right -> To the first block tag of the element of the header
#define Length(hdr)   (((hdr)>>2)&0x003FFFFF) //Shift 2 bits right to read the length of the element of the header
#define Color(hdr)    ((hdr)&3) //Read the color of the header of the element
#define Paint(hdr, color)  (((hdr)&(~3))|(color)) //Paint a color to the header of the element

#define CONSTAG 0

#define HEAPSIZE 1000 // Heap size in words

word* heap; //Where does the heap start?
word* heapTo; //Where does the copy heap start?
word* afterHeap; //Where does the heap end?
word* afterHeapTo; //Where does the copy heap end?
word* freelist; //What is free?

// These numeric instruction codes must agree with ListC/Machine.fs:
// (Use #define because const int does not define a constant in C)
#define CSTI 0
#define ADD 1
#define SUB 2
#define MUL 3
#define DIV 4
#define MOD 5
#define EQ 6
#define LT 7
#define NOT 8
#define DUP 9
#define SWAP 10
#define LDI 11
#define STI 12
#define GETBP 13
#define GETSP 14
#define INCSP 15
#define GOTO 16
#define IFZERO 17
#define IFNZRO 18
#define CALL 19
#define TCALL 20
#define RET 21
#define PRINTI 22
#define PRINTC 23
#define LDARGS 24
#define STOP 25
#define NIL 26
#define CONS 27
#define CAR 28
#define CDR 29
#define SETCAR 30
#define SETCDR 31

#define STACKSIZE 1000

// Print the stack machine instruction at p[pc]
void printInstruction(int p[], int pc) {
  switch (p[pc]) {
    case CSTI:   printf("CSTI %d", p[pc+1]); break;
    case ADD:    printf("ADD"); break;
    case SUB:    printf("SUB"); break;
    case MUL:    printf("MUL"); break;
    case DIV:    printf("DIV"); break;
    case MOD:    printf("MOD"); break;
    case EQ:     printf("EQ"); break;
    case LT:     printf("LT"); break;
    case NOT:    printf("NOT"); break;
    case DUP:    printf("DUP"); break;
    case SWAP:   printf("SWAP"); break;
    case LDI:    printf("LDI"); break;
    case STI:    printf("STI"); break;
    case GETBP:  printf("GETBP"); break;
    case GETSP:  printf("GETSP"); break;
    case INCSP:  printf("INCSP %d", p[pc+1]); break;
    case GOTO:   printf("GOTO %d", p[pc+1]); break;
    case IFZERO: printf("IFZERO %d", p[pc+1]); break;
    case IFNZRO: printf("IFNZRO %d", p[pc+1]); break;
    case CALL:   printf("CALL %d %d", p[pc+1], p[pc+2]); break;
    case TCALL:  printf("TCALL %d %d %d", p[pc+1], p[pc+2], p[pc+3]); break;
    case RET:    printf("RET %d", p[pc+1]); break;
    case PRINTI: printf("PRINTI"); break;
    case PRINTC: printf("PRINTC"); break;
    case LDARGS: printf("LDARGS"); break;
    case STOP:   printf("STOP"); break;
    case NIL:    printf("NIL"); break;
    case CONS:   printf("CONS"); break;
    case CAR:    printf("CAR"); break;
    case CDR:    printf("CDR"); break;
    case SETCAR: printf("SETCAR"); break;
    case SETCDR: printf("SETCDR"); break;
    default:     printf("<unknown>"); break; 
  }
}

// Print current stack (marking heap references by #) and current instruction
void printStackAndPc(int s[], int bp, int sp, int p[], int pc) {
  printf("[ ");
  int i;
  for (i=0; i<=sp; i++)
    if (IsInt(s[i]))
      printf("%d ", Untag(s[i]));
    else
      printf("#%d ", s[i]);
  printf("]");
  printf("{%d:", pc); printInstruction(p, pc); printf("}\n");
}


// Print current stack (marking heap references by #)
void printStack(int s[], int sp) {
  printf("[ ");
  int i;
  for (i=0; i<=sp; i++)
    if (IsInt(s[i]))
      printf("%d ", Untag(s[i]));
    else
      printf("#%d ", s[i]);      
  printf("]");
}

// Read instructions from a file, return array of instructions
int* readfile(char* filename) {
  int capacity = 1, size = 0;
  int *program = (int*)malloc(sizeof(int)*capacity); 
  FILE *inp = fopen(filename, "r");
  int instr;
  while (fscanf(inp, "%d", &instr) == 1) {
    if (size >= capacity) { 
      int* buffer = (int*)malloc(sizeof(int) * 2 * capacity);
      int i;
      for (i=0; i<capacity; i++)
        buffer[i] = program[i];
      free(program);
      program = buffer;
      capacity *= 2;
    }
    program[size++] = instr;
  }
  fclose(inp);
  return program;
}

word* allocate(unsigned int tag, unsigned int length, int s[], int sp);
void mark(word* block);
// The machine: execute the code starting at p[pc] 

int execcode(int p[], int s[], int iargs[], int iargc, int /* boolean */ trace) {
  int bp = -999;        // Base pointer, for local variable access 
  int sp = -1;          // Stack top pointer
  int pc = 0;           // Program counter: next instruction
  for (;;) {
    if (trace) 
      printStackAndPc(s, bp, sp, p, pc);
    switch (p[pc++]) {
      case CSTI:
        s[sp+1] = Tag(p[pc++]); sp++; break;
      case ADD: 
        s[sp-1] = Tag(Untag(s[sp-1]) + Untag(s[sp])); sp--; break;
      case SUB: 
        s[sp-1] = Tag(Untag(s[sp-1]) - Untag(s[sp])); sp--; break;
      case MUL: 
        s[sp-1] = Tag(Untag(s[sp-1]) * Untag(s[sp])); sp--; break;
      case DIV: 
        s[sp-1] = Tag(Untag(s[sp-1]) / Untag(s[sp])); sp--; break;
      case MOD: 
        s[sp-1] = Tag(Untag(s[sp-1]) % Untag(s[sp])); sp--; break;
      case EQ: 
        s[sp-1] = Tag(s[sp-1] == s[sp] ? 1 : 0); sp--; break;
      case LT: 
        s[sp-1] = Tag(s[sp-1] < s[sp] ? 1 : 0); sp--; break;
      case NOT: {
                  int v = s[sp];
                  s[sp] = Tag((IsInt(v) ? Untag(v) == 0 : v == 0) ? 1 : 0);
                } break;
      case DUP: 
                s[sp+1] = s[sp]; sp++; break;
      case SWAP: 
                { int tmp = s[sp];  s[sp] = s[sp-1];  s[sp-1] = tmp; } break; 
      case LDI:                 // load indirect
                s[sp] = s[Untag(s[sp])]; break;
      case STI:                 // store indirect, keep value on top
                s[Untag(s[sp-1])] = s[sp]; s[sp-1] = s[sp]; sp--; break;
      case GETBP:
                s[sp+1] = Tag(bp); sp++; break;
      case GETSP:
                s[sp+1] = Tag(sp); sp++; break;
      case INCSP:
                sp = sp+p[pc++]; break;
      case GOTO:
                pc = p[pc]; break;
      case IFZERO: { 
                     int v = s[sp--];
                     pc = (IsInt(v) ? Untag(v) == 0 : v == 0) ? p[pc] : pc+1; 
                   } break;
      case IFNZRO: { 
                     int v = s[sp--];
                     pc = (IsInt(v) ? Untag(v) != 0 : v != 0) ? p[pc] : pc+1; 
                   } break;
      case CALL: { 
                   int argc = p[pc++];
                   int i;
                   for (i=0; i<argc; i++)               // Make room for return address
                     s[sp-i+2] = s[sp-i];               // and old base pointer
                   s[sp-argc+1] = Tag(pc+1); sp++; 
                   s[sp-argc+1] = Tag(bp);   sp++; 
                   bp = sp+1-argc;
                   pc = p[pc]; 
                 } break; 
      case TCALL: { 
                    int argc = p[pc++];                  // Number of new arguments
                    int pop  = p[pc++];                  // Number of variables to discard
                    int i;
                    for (i=argc-1; i>=0; i--)    // Discard variables
                      s[sp-i-pop] = s[sp-i];
                    sp = sp - pop; pc = p[pc]; 
                  } break; 
      case RET: { 
                  int res = s[sp]; 
                  sp = sp-p[pc]; bp = Untag(s[--sp]); pc = Untag(s[--sp]); 
                  s[sp] = res; 
                } break; 
      case PRINTI:
                printf("%d ", IsInt(s[sp]) ? Untag(s[sp]) : s[sp]); break; 
      case PRINTC:
                printf("%c", Untag(s[sp])); break; 
      case LDARGS: {
                     int i;
                     for (i=0; i<iargc; i++) // Push commandline arguments
                       s[++sp] = Tag(iargs[i]);
                   } break;
      case STOP:
                   return 0;
      case NIL:    
                   s[sp+1] = 0; sp++; break;
      case CONS: {
                   word* p = allocate(CONSTAG, 2, s, sp); 
                   p[1] = (word)s[sp-1];
                   p[2] = (word)s[sp];
                   s[sp-1] = (int)p;
                   sp--;
                 } break;
      case CAR: {
                  word* p = (word*)s[sp]; 
                  if (p == 0) 
                  { printf("Cannot take car of null\n"); return -1; }
                  s[sp] = (int)(p[1]);
                } break;
      case CDR: {
                  word* p = (word*)s[sp]; 
                  if (p == 0) 
                  { printf("Cannot take cdr of null\n"); return -1; }
                  s[sp] = (int)(p[2]);
                } break;
      case SETCAR: {
                     word v = (word)s[sp--];
                     word* p = (word*)s[sp]; 
                     p[1] = v;
                   } break;
      case SETCDR: {
                     word v = (word)s[sp--];
                     word* p = (word*)s[sp]; 
                     p[2] = v;
                   } break;
      default:                  
                   printf("Illegal instruction %d at address %d\n", p[pc-1], pc-1);
                   return -1;
    }
  }
}

// Read program from file, and execute it

int execute(int argc, char** argv, int /* boolean */ trace) {
  int *p = readfile(argv[trace ? 2 : 1]);         // program bytecodes: int[]
  int *s = (int*)malloc(sizeof(int)*STACKSIZE);   // stack: int[]
  int iargc = trace ? argc - 3 : argc - 2;
  int *iargs = (int*)malloc(sizeof(int)*iargc);   // program inputs: int[]
  int i;
  for (i=0; i<iargc; i++)                         // Convert commandline arguments
    iargs[i] = atoi(argv[trace ? i+3 : i+2]);
  // Measure cpu time for executing the program
  struct rusage ru1, ru2;
  getrusage(RUSAGE_SELF, &ru1);
  int res = execcode(p, s, iargs, iargc, trace);  // Execute program proper
  getrusage(RUSAGE_SELF, &ru2);
  struct timeval t1 = ru1.ru_utime, t2 = ru2.ru_utime;
  double runtime = t2.tv_sec-t1.tv_sec+(t2.tv_usec-t1.tv_usec)/1000000.0;
  printf("\nUsed %7.3f cpu seconds\n", runtime);
  return res;
}

// Garbage collection and heap allocation 
word mkheader(unsigned int tag, unsigned int length, unsigned int color) { 
  return (tag << 24) | (length << 2) | color;
}

// Is this word in the heap?
int inHeap(word* p) {
  return heap <= p && p < afterHeap;
}

// Is this word in the heapTo?
int inToHeap(word* word){
  return heapTo <= word && word < afterHeapTo;
}

// Print this heap in a human readable way
void printHeap(word* heap) {
  word* block;
  int i;
  int j;
  printf("Heapsize: %d\n\n",HEAPSIZE);
  for (i = 0; i < HEAPSIZE; i += 1 + Length(block[0]))
  {
    block = (word*) &heap[i];
    printf("%2d: Word #%d (length: %d) \n", i, (int) &block[0], Length(block[0]));
    for (j = 1; j <= Length(block[0]); ++j){
      if (IsReference(block[j])){
        printf("%2d. Reference: %d\n", i + j, block[j]);
      }else if (block[j] == 0){
        printf("%2d. Nil\n", i + j);
      }else{
        printf("%2d. Int: %d\n", i + j, Untag(block[j]));
      }
    }
    printf("\n"); //Print a new line after every block, to make overview better
  } 
} 

//Print the heap in a readable fashion
void printHeapStats() {
  printf("\nFreelist: %d\n", (int) &(freelist[0]));

  printf("heapFrom:\n");
  printHeap(heap);

  printf("heapTo:\n");
  printHeap(heapTo);
}

void initheap() {
  //Allocate heaps
  heap = (word*)malloc(sizeof(word)*HEAPSIZE);
  heapTo = (word*)malloc(sizeof(word)*HEAPSIZE);

  //Set after heap pointers
  afterHeap = &heap[HEAPSIZE];
  afterHeapTo = &heapTo[HEAPSIZE];
  
  //Init the freelist
  freelist = &heap[0];
}

//Move a reference from heap to heapTo, and return the new reference
word* copy(word* block) {
  //Is the reference all-ready moved? Then we can just return that reference..
  if(IsReference(block[1]) && inToHeap((word*)block[1])){
    //printf("Ref# %d is in toSpace\n",(int)block[1]);
    return (word*) block[1];
  }
  
  //Allocate a block in the to-space*/
  int length = Length(block[0]);
  word* newBlock = freelist;
  freelist += length + 1;

  //Ensure that we don't exceed the heap! Should never happen, so mainly for debuging
  if(freelist > afterHeapTo){
    printf("Error: ToSpace can't hold content from FromSpace! Freelist is: %d which is bigger than %d\n",(int)freelist, (int)afterHeapTo);
    printf("FromHeap: %d - %d \n",(int)heap,(int)afterHeap);
    printf("ToHeap: %d - %d \n",(int)heapTo,(int)afterHeapTo);
    exit(1);
  }
  
  //printf("Moving word# %d. ",(int)&block[0]);
  //printf("Freelist is: %d\n",(int)freelist); 
 
  //Copy block data, including header*/
  int i;
  for(i=0; i<=length; i++)
    newBlock[i] = block[i];
  
  //Copy recursively if first block is a reference 
  //This must be done first, to "use" the value before overriding it with a forward-pointer
  if(IsReference(block[1])) newBlock[1] = (int) copy((word*) block[1]);
  
  //Update block in fromSpace to point to the new block in toSpace
  block[1] = (word) newBlock;
  
  //Recursively process words in block, if they are references
  for(i=2; i<=length; i++)
    if(IsReference(block[i])) newBlock[i] = (int) copy((word*) block[i]); 

  //Return the new block
  return newBlock;
}

//Collect grabage with a two-space stop-and-copy approach
void copyFromTo(int s[], int sp){
  //printf("##BEFORE GARBAGE COLLECTION:##\n");
  //printf("Stack:");
  //printStack(s, sp);
  //printf("\n\n");
  //printHeapStats();

  //Point freelist to begining of to-space
  freelist = &heapTo[0];

  //For all references in stack, copy necessary heap-data
  int i;
  for(i=0; i<=sp; i++)
    if(IsReference(s[i]))
      s[i] = (word) copy((word*) s[i]);

  //printf("##AFTER GARBAGE COLLECTION (before swap):##\n");
  //printf("Stack:");
  //printStack(s,sp);
  //printf("\n\n"); 
  //printHeapStats();

  //Swap the two heaps
  word* tmp = heap;
  heap = heapTo;
  heapTo = tmp;
  tmp = afterHeap;
  afterHeap = afterHeapTo;
  afterHeapTo = tmp;
}

//Do garbage collection
void collect(int s[], int sp) {
  copyFromTo(s, sp);
}

//Allocate new word with this tag of this length on this stack with this stackpointer
word* allocate(unsigned int tag, unsigned int length, int s[], int sp) {
  int attempt = 1;
  do {
    word* newBlock = freelist;
    freelist += length + 1;
    if (freelist <= afterHeap) {
      newBlock[0] = mkheader(tag, length, White);
      return newBlock;
    }
    // No free space, do a garbage collection and try again
    if (attempt==1) collect(s, sp);
  } while (attempt++ == 1);
    
  printf("Out of memory\n");
  exit(1);
}

// Read code from file and execute it
int main(int argc, char** argv) {
  if (sizeof(word)!=4 || sizeof(word*)!=4 || sizeof(int)!=4) {
    printf("Size of word, word* or int is not 32 bit, cannot run\n");
    return -1;
  } else if (argc < 2) {
    printf("Usage: listmachine [-trace] <programfile> <arg1> ...\n");
    return -1;
  } else {
    int trace = argc >= 3 && 0==strncmp(argv[1], "-trace", 7);
    initheap();
    return execute(argc, argv, trace);
  }
}
