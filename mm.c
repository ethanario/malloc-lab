/*
 * How the allocator works:
 * 
 * 1. Footers are removed from allocated blocks and the header 
 * 	of the next block will have its penultimate bit set to one 
 * 	(add 0x2) if the previous block is allocated. Free blocks still have both
 * 	a header and a footer
 * 2. I chose to use a segregated list with best fit but the number of 
 * 	iterations allowed is limited because the allocater runs faster and 
 * 	utility was already quite good. There are 10 lists that are used for the segregated list
 *  and for each list the size of allowed blocks increases by a factor of 2. New blocks
 *  are inserted at the front (LIFO). Each block has a pointer to the next and previous 
 *  block in the same list. 
 * 3. Small blocks (payload of eight bytes or less) are placed in a seperate list. If a block
 * 	is a small block, the then 0x4 is added to the header of the next block
 * 	ie. the third free bit. The total size of the small blocks is 16 so we dont store
 * 	a pointer to the previous free block in the list, just the next block
 */


/* Do not change the following! */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */

//#define DEBUG // uncomment this line to enable debugging
#ifdef DEBUG

/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#define dbg_checkheap(...) mm_checkheap(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#define dbg_checkheap(...)
#endif 

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*sizeof(word_t);       // double word size (bytes)
static const size_t min_block_size = 4*sizeof(word_t); // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

#define num_of_lists 10
#define iteration_cap 200
#define next_from_pointer block->payload.free_block_pointers.next
#define prev_from_pointer block->payload.free_block_pointers.prev
#define prev_alloc_mask 0x2
#define prev_small_mask 0x4
static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;


typedef struct block block_t;
/* Blocks have:
 * 1. A header that contains size, allocation flag, previous allocation flag
 * 	and whether the previous block is a small block
 * 2. A payload that has only data if it is alocated or pointers to the next 
 * 	and previous free blocks if it is free and not a small block. Small blocks
 * 	only have a pointer to the next free small block. Because the payload will carry
 * 	either pointers or data but not both, we use a union
 */
struct block
{
	word_t header;
	union{
		struct
		{
			block_t *next;
			block_t *prev;
		}free_block_pointers;
		char data[0];	
   }payload;
};



//Pointer to first block 
static block_t *heap_start = NULL;
//Pointer to list of the small blocks
static block_t *small_blocks_list = NULL;
//Array of pointers for segregated list
static block_t *seg_list_pointers[num_of_lists];

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

bool mm_checkheap(int lineno);
static void add_to_list(block_t *block, size_t size);
static void remove_from_list(block_t *block);
static int get_list_num(size_t size);
static bool check_prev_alloc(block_t *block);

/* 
 * Takes a block and its size and inserts it into the correct list. Uses get_num_list()
 */
static inline void add_to_list(block_t *block, size_t size)
{
	// Small blocks
	if (size<=dsize)
	{
		next_from_pointer = small_blocks_list;
		small_blocks_list = block;
	}
	
	//Not small blocks
	else
    {   
        int list_num = get_list_num(size);
        
        //Next free block pointer is set to the start of the list
        next_from_pointer = seg_list_pointers[list_num];
        
        //Set the prev pointer of the block that used to be first
        if(seg_list_pointers[list_num]!= NULL)
            seg_list_pointers[list_num]->payload.free_block_pointers.prev = block;
        
        //Set the start of the list to the new block
        seg_list_pointers[list_num] = block;
        
        //At the front of the list so the previous pointer is null
		prev_from_pointer = NULL;
        return;
    }    
}

/*
 * Takes a block and removes it from its list
 */
static inline void remove_from_list(block_t *block)
{ 
    size_t size = get_size(block);

    block_t *prev_block;
    block_t *small_list_pointer;
    block_t *next_block, *prv;
    int list_num;
    
    // Delete from small blocks list for small sizes
    if(size<=dsize){
        small_list_pointer = small_blocks_list;
        
        //Iterate through the list of small blocks
        while(small_list_pointer!=NULL)
        {
            if(small_list_pointer == block && small_list_pointer == small_blocks_list)
            {   
				small_blocks_list = small_list_pointer->payload.free_block_pointers.next;
				return;
            }
            else if(small_list_pointer == block){
                prv->payload.free_block_pointers.next = small_list_pointer->payload.free_block_pointers.next;
                return;
            }
            prv = small_list_pointer;
            small_list_pointer = small_list_pointer->payload.free_block_pointers.next;
        }
    }
    
    // Check if it is not a small block
    else
    {
        next_block = next_from_pointer;
        prev_block = prev_from_pointer;
        
        if(prev_block == NULL){
        	list_num = get_list_num(size);
			seg_list_pointers[list_num] = next_block;   
        }
        else
        	prev_block->payload.free_block_pointers.next = next_block;    
    
        //Set the prev pointer of the next block
		if(next_block != NULL)
			next_block->payload.free_block_pointers.prev = prev_block;
    
    return;
    }
}   

/* 
 * Returns the list number that a given block fits in 0-10
 */
static int get_list_num(size_t size){
	if(size<=16)
	    return -1;
	
	if((size>16) && (size<=32))
        return 0;
	
    if((size>32) && (size<=64))
        return 1;
    
    if((size>64) && (size<=128))
        return 2;
    
    if((size>128) && (size<=256))
        return 3;
    
    if((size>256) && (size<=512))
        return 4;
    
    if((size>512) && (size<=1024))
        return 5;
    
    if((size>1024) && (size<=2048))
        return 6;
    
    if((size>2048) && (size<=4098))
        return 7;
    
    if((size>4098) && (size<=8192))
        return 8;
    
    if(size>8192)
        return 9;
    
    dbg_printf("No list found");
    return 999;
}


/*
 * mm_init: initializes the heap and points
 * heap_start at the epilogue header.
 */
bool mm_init(void) 
{
    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));
    int i;
    if (start == (void *)-1) 
    {
        return false;
    }

    start[0] = pack(0, true); // Prologue footer
    start[1] = pack(0, true); // Epilogue header
    start[1] |= prev_alloc_mask; //set previous block allocated flag 
    
    // Heap starts with first block header (epilogue)
    heap_start = (block_t *) &(start[1]);
    
    //Initialize the pointers for the free block lists
    for(i=0; i<num_of_lists; i++)
        seg_list_pointers[i] = NULL;  
    small_blocks_list = NULL;
    
    // Extend the empty heap with a free block of chunksize bytes
    dbg_ensures(mm_checkheap(__LINE__));
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    dbg_checkheap(__LINE__);
    return true;
}

/*
 * malloc: Checks if the heap is initialized and if it is not, call mm_init.
 * Then creates a block of a given size then rounds up so at to be alligned 
 * with the heap. Once the block is created, insert it into the heap with find_fit()
 * and then either place it or extend the heap as needed
 */
void *malloc(size_t size) 
{

    dbg_checkheap(__LINE__); 
    
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
    	dbg_ensures(mm_checkheap(__LINE__));
    	return bp;
    }

   // If the payload is < 9 bytes, then we make a small block instead 
   if(size<9)
   {
        asize = min_block_size/2;
   }
   
   // If size is less than double word size (dsize), the block will be the minimum
   else if (size <= dsize)
   {        
        asize = min_block_size;
   }
   
   // Adjust block size to include overhead and to meet alignment requirements    
   else
        asize = round_up(size+wsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {  
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }
    }
    
    place(block, asize);
    bp = header_to_payload(block);
    dbg_checkheap(__LINE__);
    
    return bp;
} 
/*
 * free: Frees the block such that it is no longer allocated while still
 * maintaining its size. Block will be available for use on malloc.
 */
void free(void *bp)
{
    block_t *next_block;
    int is_prev_allocated,is_prev_small;

    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);
    
    // Check whehter the previous block is allocated, small or both
    is_prev_allocated = (block->header) & prev_alloc_mask;
    is_prev_small = (block->header) & prev_small_mask;
    
    //Get the size
    size_t size = get_size(block);
    
    // Carry over allocated and small flags to the new block
    write_header(block, size+is_prev_allocated+is_prev_small, false);
    write_footer(block, size, false);
    next_block = find_next(block);
    
    // Update the header of the next block
    next_block->header &= (~prev_alloc_mask);

    coalesce(block);
    dbg_checkheap(__LINE__);
}

/*          
 * realloc: takes *ptr which points to a block and if size is greater than 
 * the current size of the block, reallocate the block to an appropriate location 
 * and return the pointer to the new position. If size = 0, then free 
 * the block and return NULL. 
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
    size_t payload_size;
    void *newptr;

    // If size == 0, then free the block
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If the ptr is NULL, then treat it as a call to malloc(size)
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Try calling malloc(size)
    newptr = malloc(size);
    if (!newptr)
    {
        return NULL;
    }

    // If malloc(size) works, then transfer the data to the new block
    payload_size = get_payload_size(block);
    if(size < payload_size)
    {
    	payload_size = size;
    }
    
    //Copy the memory of size payload_size from ptr to newptr
    memcpy(newptr, ptr, payload_size);

    // Free the old block
    free(ptr);
    dbg_checkheap(__LINE__);

    return newptr;
}

/*
 * calloc: calls malloc on the aligned size, then sets all allocated 
 * bits t *bp to 0 using memset
 */
void *calloc(size_t elements, size_t size)
{
	void *bp;
	size_t asize = elements * size;
	
	if (asize/elements != size){
		// Multiplication overflowed
		return NULL;
	}
	
	bp = malloc(asize);
	if (bp == NULL)
	{
		return NULL;
	}
	// Initialize all bits to 0
	memset(bp, 0, asize);
	dbg_checkheap(__LINE__);

	return bp;
}

/*             
 * extend_heap: Extends the heap by size. Rewrites the epilogue header and carries
 * over the flag information into the newly created block. Coalesces then returns
 * the pointer to the new block
 */
static inline  block_t *extend_heap(size_t size) 
{
    //Get the epilogue
    void *epilogue = ((char *)(mem_heap_hi())-7); 
    
    /*Check if the block before the epilogue is allocated and 
     * if it is allocated, check if it is a small block
     */
    long epilogue_prev_alloc = (prev_alloc_mask)&(*((long *)(epilogue)));
    long epilogue_prev_small = (prev_small_mask)&(*((long *)(epilogue)));
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    write_header(block, size, false);
    
    /* Write the previous allocated and the previous small block flags to
     * the new block as appropriate
     */ 
    block->header |= (epilogue_prev_alloc)|(epilogue_prev_small);
    write_footer(block, size, false);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    block_next->header = 0;
    write_header(block_next, 0, true);
    
    return coalesce(block);
}

/* check_prev_alloc: Checks whether the previous block is allocated by looking at 
 * the penultimate bit of the block header
 */
static bool check_prev_alloc(block_t *block)
{
    return((block->header)&prev_alloc_mask);
}

/* Coalesce: Checks which of the adjacent blocks are free and coalesces them and 
 * returns the pointer to the new block. Updates the headers and flags of the 
 * adjacent block and adds the free block into the linked lists
 */
static inline block_t *coalesce(block_t * block) 
{
    block_t *prev_block, *temp_next; 
    size_t size = get_size(block);
    block_t *block_next = find_next(block);
    
    // Check if the previous block is a small block
    if(block->header & prev_small_mask){
        prev_block = (block_t *)(((char *)block)-dsize);
    }
    else
    	prev_block = find_prev(block);
    
    //Check whether the previous and next blocks are allocated
    bool prev_alloc = check_prev_alloc(block);
    bool next_alloc = get_alloc(block_next);

	//If both next and previous blocks are allocated
    if (prev_alloc && next_alloc){
        add_to_list(block,size);
        return block;
    }
    
    //Next block is unallocated
    else if (prev_alloc && !next_alloc){
        size += get_size(block_next); 
        remove_from_list(block_next);
        
        // If next block is small update the header of the new next block
        if(get_size(block_next)<=dsize)
        {
            temp_next = find_next(block_next);
            temp_next->header &= (~prev_small_mask);
        }
        
        //Clear the header of the unused next block
        block_next->header = 0;
        
        // Write the header and set the prev_alloc_mask
        write_header(block, size+prev_alloc_mask, false);
        write_footer(block, size+prev_alloc_mask, false);
        add_to_list(block,size);
        return block;
    }
    
    //Previous block is unallocated
    else if (!prev_alloc && next_alloc){
        size += get_size(prev_block);
        remove_from_list(prev_block);
        
        // Update the header of the new block with prev_alloc_mask
        write_header(prev_block, size+prev_alloc_mask, false);
        write_footer(prev_block, size+prev_alloc_mask, false);
       
        // If next block is small update the header of the new next block
        if(get_size(block)<=dsize)
        {
            temp_next = block_next;
            temp_next->header &= (~prev_small_mask);
        }
        
        //Clear the header of the now unused block
        block->header = 0;
        
        //Add the new block to the free blocks lists
        add_to_list(prev_block,size);
        return prev_block;
    }
    
    //Both adjacent blocks are unallocated
    else{
        size += get_size(block_next) + get_size(prev_block);
        
        //Remove both adjacent blocks from the free lists
        remove_from_list(prev_block);
        remove_from_list(block_next);
        
        // If next block is small update the header of the new next block
        if(get_size(block_next)<=dsize)
        {
            temp_next = find_next(block_next);
            temp_next->header &= (~prev_small_mask);
        }
        
        //Clear the header of the now unused block
        block_next->header = 0;
        block->header = 0;
        
        // Write the header and set the prev_alloc_mask
        write_header(prev_block, size+prev_alloc_mask, false);
        write_footer(prev_block, size+prev_alloc_mask, false);
        
        //Add the new block to the free lists
        add_to_list(prev_block,size);
        return prev_block;
    }
    return block;
}

/*       
 * place: Places a block with asize and checks if the remaining size is large enough
 * for another block. If it is then free the remainder and update all headers
 */
static void place(block_t *block, size_t asize)
{
    // Extract prev_alloc_mask and prev_small_mask in current block
    int is_prev_allocated = (block->header)&(prev_alloc_mask);
    int is_prev_small = (block->header)&(prev_small_mask);
    
    size_t csize = get_size(block);

    block_t *block_next;
    remove_from_list(block);
    
    if ((csize - asize) >= min_block_size/2){
        // write the header to the block
        write_header(block, asize+is_prev_allocated+is_prev_small, true);
        block_next = find_next(block);
        block_next->header = 0;
        
        // Set prev_small_mask if it is a small block
        if(asize==dsize)
            is_prev_small = prev_small_mask;
        else
            is_prev_small = 0;
        
        // Set prev_alloc_mask and prev_small_mask accordingly in the new block
        write_header(block_next,csize-asize+prev_alloc_mask+is_prev_small,false);
        write_footer(block_next, csize-asize, false);
        coalesce(block_next);
    }
    else{ 
        write_header(block, csize+is_prev_allocated, true);
        
        // Check if it is small block and update the next header 
        if(csize==dsize)
        {
            block_next = find_next(block);
            block_next->header |= (prev_small_mask);
        }
    }
}

/*           
 * find_fit: Uses get_list_num() to figure out which of the free lists to check,
 * then loop through that list up to the number of times specified by iteration_cap 
 * (200 times) and returns the pointer to the smallest block that can hold asize 
 */
static inline block_t *find_fit(size_t asize)
{
    block_t *block, *best_fit = NULL;
    int list_num = get_list_num(asize);
    int i;
	int iteration_counter=0;
    size_t block_size = mem_heapsize();
    size_t curr_block_size; 
    
    // Check whether to search in the small blocks list instead. Return the first small block
    if( list_num==-1){
    	block = small_blocks_list;
        
    	//Iterate through the list
    	while(block!=NULL)
        {   
            curr_block_size = get_size(block);
            if(asize <= curr_block_size)
            	return block;
            
            block = next_from_pointer;
        }
        //If no free block in the small list, try again starting with the smallest linked list
        list_num = 0;
    }
    
    /* Check the list given by list_num. Move on to the next list if there are no 
     * free blocks in that list
     */
    for(i=list_num; i<num_of_lists; i++){
    	//Check the first block in the list
        block = seg_list_pointers[i];
       
        //Iterate through the list
        while(block != NULL){   
            curr_block_size = get_size(block);
            if(asize<curr_block_size){   
                // Iterate through until the iteration_cap is met and return the block
                if(iteration_counter++ == iteration_cap)
                	return best_fit;
                
                //Check if the new block is the current best fit
                if((curr_block_size)<(block_size)){
                    block_size = curr_block_size;
                    best_fit = block;
                }
            }
            
            // If sizes match perfectly, return the block immediately
            else if(asize==curr_block_size){
                return block;
            }
            block = next_from_pointer;
        }
    }
    return best_fit;
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc)
{
    return alloc ? (size | 1) : size;
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - wsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header. 
 *               It also sets the prev_small_mask and prev_alloc_mask in the next block 
 *               accordingly.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
    block_t *next_block;
    
    // If its a small block update the next header
    if((size & size_mask) == dsize){
    	//Get the next block by adding dsize if its a small block and update the header
        next_block = (block_t *)(((char*)block)+dsize);
        next_block->header |= prev_small_mask;
    }
    
    // Update header with pack
    block->header = pack(size|(block->header & prev_small_mask), alloc);
    
    // If the block is allocated update the next header unless its the prologue or epilogue
    if(alloc){
        next_block = find_next(block);   
        if(next_block==block)
            return;
        next_block->header |= (prev_alloc_mask);
    }
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
   
    word_t *footerp;
    
    // Don't write the footer if its a small block
    if(size<=dsize)
        return;
    
    footerp = (word_t *)((block->payload.data) + get_size(block) - dsize);
    *footerp = pack(size, alloc);
}


/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));
    
    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload.data);
}

/* mm_checkheap: checks the heap for correctness; returns true if
 *               the heap is correct, and false otherwise.
 *               can call this function using mm_checkheap(__LINE__);
 *               to identify the line number of the call site.
 */
bool mm_checkheap(int lineno)  
{ 
    dbg_printf("\nLine: %d", lineno);
    
   //Check the heap boundaries
    void *prologue = mem_heap_lo();
    void *epilogue = mem_heap_hi();
    epilogue = (((char *)epilogue)-7); 
    long epilogue_bit = *((long *)epilogue);
    long prologue_bit = *((long *)prologue);
    
    if(!(epilogue_bit & 0x1) ||  !(prologue_bit & 0x1)){
        printf("Error: Prologue or epilogue does not equal 1!");
        printf("\nPrologue bit: %lx, Epilogue bit: %lx", prologue_bit, epilogue_bit);   
    }  
    
    block_t *block = (block_t *)((long *)prologue+1);
    
    
    int header_counter=1;
    int is_allocated,is_next_allocated;
    int free_block_total = 0, allocated_block_total=0;
    size_t block_size;
    
    //Loop through each block until the end of the heap is reached
    while((long)block != (long)epilogue )
    {   
		is_allocated = get_alloc(block);
    	
    	//Print the heap
		dbg_printf("\nPrologue:      %p",prologue);
		dbg_printf("\n  Header %d:    %p      ",header_counter,block);
		dbg_printf("Allocated: %s", is_allocated ? "yes" : "no");
		dbg_printf("\n   Payload     %p",header_to_payload(block));
		dbg_printf("\n   Size:              %lx",get_payload_size(block));
		
		//Make sure everything is 16 byte aligned
		if( ((long)header_to_payload(block))%16 != 0)
		{
			printf("\nError: Payload adress not aligned at %p",header_to_payload(block));
			return false;
		}

		/*Check whether the block is allocated and add it to the count of
		 * either free or allocated blocks 
		 */
		if(!is_allocated)
        {
            free_block_total++;
        }
        else
            allocated_block_total++;
		
        block_size = get_size(block);

        
        //Check coalescing of the next block 
        block = find_next(block);
        is_next_allocated = get_alloc(block);
        if(!is_allocated && !is_next_allocated)
        {
            printf("\nError: Two adjacent free blocks");
            return false;
        }

        //Check the flags of the next block
        if(block!=NULL && block_size <= dsize)
        {
            if(!(block->header&prev_small_mask))
            {
                printf("Error: Small block flag not set\n");
                return false;
            }
        }
        header_counter++;
    }
	dbg_printf("\nEpilogue:      %p",epilogue);
	dbg_printf("\nTotal free blocks: %d",free_block_total);
	dbg_printf("\nTotal allocated blocks: %d", allocated_block_total);

	//Checking the seg lists
    int blocks_in_seg_list = 0;
    block_t *ptr, *next, *prev;
    int current_list = 0;
    for(current_list=0; current_list < num_of_lists; current_list++)
    {
        //Set the pointer to the start of the current list
    	ptr = seg_list_pointers[current_list];
    	
    	//Loop through the list
		while(ptr!=NULL)
		{
			//The pointers to the next and previous blocks
			next = ptr->payload.free_block_pointers.next;
			prev = ptr->payload.free_block_pointers.prev;
			
			//Update the count of blocks in the seg list
			blocks_in_seg_list++;    

			//Make sure all blocks in the list are free
			if(get_alloc(ptr))
			{
				 printf("\nFree block found in seg list");
				 return false;
			}
			
			if(next!=NULL)
			{
				if(next->payload.free_block_pointers.prev != ptr)
				{
					printf("\nPrevious pointer of the next block is incorrect");  
					printf("prev: %p, next: %p",prev,next);
					return false;
				}
			}
			
			if(prev!=NULL)
			{
				if(prev->payload.free_block_pointers.next!=ptr)
				{
					printf("\nPrevious pointer of the next block is incorrect: ");
					printf("prev: %p, next: %p",prev,next);
					return false;
				}
			}       
			
			//Check that free blocks are in the right list
			if(get_list_num(get_size(ptr))!=current_list)
			{
				 printf("\nFree block is in the wrong list");
				 return false;
			}

			ptr = next;
		}
	}
	dbg_printf("\n\n\n\n");
    
    return true;

}
