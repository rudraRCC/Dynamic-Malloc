/* 
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP2e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */
//Eni maa no atthho
//Eni maa no navvo
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"R&K\n",
	/* First member's full name */
	"Rudra\n",
	/* First member's email address */
	"201401129@daiict.ac.in\n",
	/* Second member's full name (leave blank if none) */
	"Kevin\n",
	/* Second member's email address (leave blank if none) */
	"201401014@daiict.ac.in\n"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

//user time pass

struct freeblocknode
{
	struct freeblocknode *previous;
	void *freeblockptr;
	struct freeblocknode *next;
};

struct freeblocknode freeblock[40];

/*for(i=0;i<24;i++)
{
	freeblock[i].previous = NULL;
	freeblock[i].freeblockptr = NULL;
	freeblock[i].next = NULL;
}*/
//user time pass ends

/* Global variables: */
static char *heap_listp; /* Pointer to first block */  

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
//static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static void *find_best_fit(size_t asize);


/* fFunction prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

//user time pass
int indexlog2(long int);
int indexdiv8(int);
void removefromlist(void *);
void addtolist(void *,int);
//user time pass ends
/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void) 
{

	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
		return (-1);
	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (2 * WSIZE);

	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (-1);
	
	//user time pass
	int initialindex = indexlog2(GET_SIZE(HDRP((int *)heap_listp)));
	printf("size of initial heap %ld\n",GET_SIZE(HDRP((int *)heap_listp)));
	printf("initial index = %d\n",initialindex);
	static struct freeblocknode newnode;
	newnode.freeblockptr = (void *)((int *)heap_listp );	
	printf("value of heaplistp %d\n",*((int *)heap_listp + 1f));
	//printf("value of fbp in newnode %d\n",*(int *)newnode.freeblockptr);
	freeblock[initialindex].next = &(newnode);
	newnode.previous = &(freeblock[initialindex]);
	//printf("initial index %d\n",initialindex);
	if(freeblock[initialindex].next->freeblockptr != NULL)	
		printf("value of fbp 1 %d\n",*(int *)freeblock[initialindex].next->freeblockptr);
	printf("size of initial fbp in init %ld\n",GET_SIZE(HDRP((int *)heap_listp)));	
	//user time pass ends
	return (0);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{	
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

	/* Search the free list for a fit. */
	
	if(freeblock[36].next->freeblockptr != NULL)	
		printf("value of fbp in malloc %d\n",*(int *)freeblock[36].next->freeblockptr);
	printf("size of initial heap in malloc %ld\n",GET_SIZE(HDRP((int *)heap_listp + 1)));
	bp = find_best_fit(asize);
	if(bp != NULL)
		printf("bp is not NULL\n");
	printf("size of bp %ld\n",GET_SIZE(HDRP((int *)bp)));
	if (bp != NULL) {
		printf("in malloc before place\n");
		place(bp, asize);
		printf("in malloc after place\n");
		//need to check for allocated block and size class (using log) if bp has been split. did that in place function.
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	place(bp, asize);
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.= %d\n
 */
void
mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *
mm_realloc(void *ptr, size_t size)
{
	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(size));

	newptr = mm_malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if (newptr == NULL)
		return (NULL);

	/* Copy the old data. */
	oldsize = GET_SIZE(HDRP(ptr));
	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);

	return (newptr);
}

/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *
coalesce(void *bp) 
{
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));	
	
	//add the blocks to corresponding size class after checking (using log).
	if (prev_alloc && next_alloc) {    		/* Case 1 */
		return (bp);
	} else if (prev_alloc && !next_alloc){         /* Case 2 */
		//user time pass	
		void* nextblkptr = NEXT_BLKP(bp);
		removefromlist(nextblkptr);
		//user time pass ends
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		
	} else if (!prev_alloc && next_alloc) {         /* Case 3 */
		//user time pass	
		void* prevblkptr = PREV_BLKP(bp);
		removefromlist(prevblkptr);
		//user time pass ends
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	} else {                                        /* Case 4 */
		//user time pass	
		void* nextblkptr = NEXT_BLKP(bp);
		removefromlist(nextblkptr);
		void* prevblkptr = PREV_BLKP(bp);
		removefromlist(prevblkptr);
		//user time pass ends
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}
	
	//user time pass
	addtolist(bp,size);
	//user time pass ends
	
	return (bp);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words) 
{
	void *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	/* Coalesce if the previous block was free. */
	return (coalesce(bp));
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */

static void *
find_best_fit(size_t asize)
{
	//unsigned int minsize = 100000000;
	//void *bp;
	void *toallocate = NULL;
	//int flag =0;	

	//user time pass
	int startindex = indexlog2(asize);
	int i;
	for(i=startindex;i<40;i++)
	{
		if(freeblock[i].next != NULL)
		{
			printf("if running %d\n",i);
			printf("value of fbp %d\n",*(int *)freeblock[i].next->freeblockptr);
			printf("size of freeblockptr in best fit %ld\n",GET_SIZE(HDRP((int *)freeblock[i].next->freeblockptr)));
			toallocate = freeblock[i].next->freeblockptr;
			if(freeblock[i].next->freeblockptr == NULL)
				printf("freeblockptr is	 null\n");
			if(toallocate == NULL)
				printf("to allocate null\n");
			struct freeblocknode *temp = freeblock[i].next;
			if(temp->next != NULL)
				freeblock[i].next = temp->next;
			if(freeblock[i].next != NULL)
				(freeblock[i].next)->previous = temp->previous;
			printf("before return\n");
			return (void*)(toallocate);
		}
	}
	
	return NULL;
	//user time pass ends

	/* Search for the best fit. */
        /*for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
                if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp)))
		{
			if(GET_SIZE(HDRP(bp)) < minsize)
			{
				minsize = GET_SIZE(HDRP(bp));
				toallocate = bp;
				flag = 1;
			}
		}
		if(minsize == asize)
			break;
        }
	
	if(flag == 1)
		return toallocate;
	return NULL;*/
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void
place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   
	printf("asize in place %d\n",(int)asize);
	printf("in place %lu\n",csize);
	if ((csize - asize) >= (2 * DSIZE)) { 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		printf("size using hdr %ld\n",GET_SIZE(HDRP((int *)bp)));
		if(FTRP(bp) != NULL)
			printf("ftr is not null\n");		
		PUT(FTRP(bp), PACK(csize - asize, 0));
		printf("%ld \n",csize-asize);
		printf("size using ftr %ld\n",GET_SIZE(FTRP((int *)bp)));
		//user time pass
		printf("in place before addtolist\n");
		addtolist(bp,csize-asize);		
		printf("in place after addtolist\n");		
		//user time pass ends
	} else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
}

/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *bp) 
{

	if ((uintptr_t)bp % DSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void
checkheap(bool verbose) 
{
	void *bp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
	    !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp) 
{
	bool halloc, falloc;
	size_t hsize, fsize;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
	    hsize, (halloc ? 'a' : 'f'), 
	    fsize, (falloc ? 'a' : 'f'));
}

int indexlog2(long int x)
{
	int i;
	for(i=0;x>1;i++)
	{
		x=x/2;
	}
	return i;
}

int indexdiv8(int x)
{
	int y = x/8;
	if(!(x & 0x7))
	y++;
	return y;
	
}

void removefromlist(void *ptr)
{
	int blksize = GET_SIZE(HDRP(ptr));
	int index = indexlog2(blksize);

	struct freeblocknode *removenode = freeblock[index].next; 
	while(removenode->freeblockptr != ptr)
	{
		removenode = removenode->next;
	}
	
	struct freeblocknode *prev = removenode->previous;	
	struct freeblocknode *next = removenode->next;
		
	prev->next = removenode->next;
	next->previous = removenode->previous;		
}

void addtolist(void *ptr,int sizex)
{
	int index = indexlog2(sizex);
	printf("index in addtolist %d\n",index);
	struct freeblocknode *temp = freeblock[index].next;
	struct freeblocknode newnode; 		
	newnode.freeblockptr = ptr;
	newnode.next = temp;
	newnode.previous = &(freeblock[index]);
	if(temp->previous != NULL)
		temp->previous = &(newnode);
	freeblock[index].next = &(newnode);
}
/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */
