#ifndef _STACK_H
#define _STACK_H

#define DEFINE_PRINT_STACK_FUNCTION 1

/* Defining the type of the stack's elements */
typedef int stack_elem;

/* A stack is defined as a pointer to an item */
typedef struct item item;
typedef item* stack;

/* An item in the stack is defined as a struct containing the value of the current item (head)
 *  and a pointer to the next item in the stack (tail)
 * An item is considered to be the last of the stack if its tail is the null pointer.
 */
struct item {
  stack_elem head;
  stack tail;
};

/* ------------------------ Functions ------------------------ */

/* @requires: nothing
 * @assigns: nothing
 * @ensures: returns an empty stack (ie. a null pointer)
 */
stack create_stack();

/* @requires: s is a valid stack
 * @assigns: nothing
 * @ensures: returns 1 if s is an empty stack, 0 otherwise
 */
int is_stack_empty(stack s);

/* @requires: s is a valid stack and doesn't loop
 * @assigns: creates a new stack
 * @ensures: returns a reversed copy of s
 */
stack reverse_stack(stack s);

/* @requires: s is a valid stack
 * @assigns: creates a new stack and copies each element of s in the new stack, in the same order
 * @ensures: returns a copy of the stack s
 */
stack copy_stack(stack s);

/* @requires: s is a valid stack and doesn't loop
 * @assigns: creates a new stack and pushes each element of s in it in a random order
 * @ensures: returns a shuffled copy of the stack s
 */
stack shuffle_stack(stack s);

/* @requires: *s is a valid stack
 * @assigns: modifies s
 * @ensures: adds e to the begginning of s
 */
void push(stack_elem e, stack* s);

/* @requires: *s is a valid, non empty stack
 * @assigns: modifies s
 * @ensures: removes the first element of the stack and returns it
 */
stack_elem pop(stack* s);

/* @requires: s is a valid, non empty stack
 * @assigns: nothing
 * @ensures: returns the first element of s
 */
stack_elem peek(stack s);

/* @requires: *s is a valid stack and doesn't loop
 * @assigns: modifies the stack
 * @ensures: adds e at the end of *s
 */
void push_last(stack_elem e, stack* s);

/* @requires: *s is a valid, non-empty stack and doesn't loop
 * @assigns: modifies the stack
 * @ensures: removes the last element of the stack and returns it
 */
stack_elem pop_last(stack* s);

/* @requires: s is a valid, non empty stack and doesn't loop
 * @assigns: nothing
 * @ensures: returns the last element of s
 */
stack_elem peek_last(stack s);

/* @requires: s is a valid stack, 0 <= index < stack_len(s)
 * @assigns: nothing
 * @ensures: returns the index-th stack_element of s
 */
stack_elem get_stack_elem(stack s, int index);

/* @requires: *s is a valid stack, 0 <= index < stack_len(*s)
 * @assigns: changes the index-th element of the stack to e
 * @ensures: changes the index-th element of the stack to e
 */
void set_stack_elem(stack *s, stack_elem e, int index);

/* @requires: *s is a valid stack, 0 <= index <= stack_len(*s)
 * @assigns: modifies the stack
 * @ensures: inserts the stack_element e at the index-th place in the stack
 */
void insert_stack_elem(stack* s, stack_elem e, int index);

/* @requires: *s is a valid stack, 0 <= index < stack_len(*s)
 * @assigns: modifies the stack
 * @ensures: removes the index-th element of the stack, frees the memory previously allocated to it and returns the element removed
 */
stack_elem pop_stack_elem(stack *s, int index);

/* @requires: *s is a valid stack, 0 <= i1, i2 < stack_len(*s)
 * @assigns: modifies the stack
 * @ensures: switch the e1-th and the e2-th elements of the stack
 */
void switch_stack_elem(stack *s, int e1, int e2);

/* @requires: s is a valid stack and (e is in s or s doesn't loop)
 * @assigns: nothing
 * @ensures: returns the index of the first occurence of e in s, or -1 if e is not in s
 */
int seek_stack_elem(stack_elem e, stack s);

/* @requires: s is a valid stack and doesn't loop
 * @assigns: nothing
 * @ensures: returns the length of s (ie. the number of elements it contains)
 */
int stack_len(stack s);

/* @requires: *s is a valid stack and doesn't loop
 * @assigns: frees the memory used by each item of the stack
 * @ensures: frees the memory used by the stack
 */
void free_stack(stack* s);

/* @requires: s is a valid stack and doesn't loop
 * @assigns: nothing
 * @ensures: prints the stack s in the format [stack_elem1] -> [stack_elem2] -> ... -> []
 */
#if DEFINE_PRINT_STACK_FUNCTION >= 1
void print_stack(stack s);
#endif


#endif
