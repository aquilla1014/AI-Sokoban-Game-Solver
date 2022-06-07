/*
 * Assignment 3, Aishwarya Hirve
 * Algorithms and Data Structures
 * Submitted on 24th October, 2021 (with an approved 48h extension)
 */

#include <time.h>
#include <stdlib.h>
#include <limits.h>
#include <math.h>

#include "ai.h"
#include "utils.h"
#include "hashtable.h"
#include "priority_queue.h"

/**
 * Retrieve solution and return a string containing the squence of moves
*/
char* save_solution( node_t* solution_node ){
    node_t* n = solution_node;
    char *solution_string = malloc( sizeof( char ) * solution_node->depth + 1 );
    solution_string[ n->depth ] = '\0';
    while ( n->parent != NULL )
    {
        switch ( n->move ) {
        case up:
            if ( n->parent->state.map[ n->state.player_y ]
                [ n->state.player_x ] == '$')
                solution_string[ n->depth-1 ] = 'U';
            else
                solution_string[ n->depth-1 ] = 'u';
            break;

        case down:
            if ( n->parent->state.map[ n->state.player_y ]
                [ n->state.player_x ] == '$')
                solution_string[ n->depth-1 ] = 'D';
            else
                solution_string[ n->depth-1 ] = 'd';
            break;

        case left:
            if ( n->parent->state.map[ n->state.player_y ]
                [ n->state.player_x ] == '$')
                solution_string[ n->depth-1 ] = 'L';
            else
                solution_string[ n->depth-1 ] = 'l';
            break;

        case right:
            if ( n->parent->state.map[ n->state.player_y ]
                [ n->state.player_x ] == '$')
                solution_string[ n->depth-1 ] = 'R';
            else
                solution_string[ n->depth-1 ] = 'r';
            break;
        }
        n = n->parent;
    }
    return solution_string;
}

/**
 * Copy a src into a dst state
*/
void copy_state( sokoban_t* init_data, state_t* dst, state_t* src ){

    dst->map = malloc( sizeof( char * ) * init_data->lines );
    for ( int i = 0; i < init_data->lines; ++i ){
        int width = strlen( src->map[i] ) + 1;
        dst->map[i] = malloc( width );
        memcpy(dst->map[i], src->map[i], width );
    }

    dst->player_x = src->player_x;

    dst->player_y = src->player_y;

}

/**
 * Create the initial node
*/
node_t* create_init_node( sokoban_t* init_data ){
    node_t * new_n = (node_t *) malloc(sizeof(node_t));
    new_n->parent = NULL;
    new_n->priority = 0;
    new_n->depth = 0;
    new_n->num_childs = 0;
    new_n->move = -1;
    new_n->state.map = malloc( sizeof( char * ) * init_data->lines );
    for ( int i = 0; i < init_data->lines; ++i )
    {
        int width = strlen( init_data->map[i] ) + 1;
        new_n->state.map[i] = malloc( width );
        memcpy(new_n->state.map[i], init_data->map[i], width);
    }
    new_n->state.player_x = init_data->player_x;
    new_n->state.player_y = init_data->player_y;
    return new_n;
}

/**
 * Create the a node from a parent node
*/
node_t* create_node( sokoban_t* init_data, node_t* parent ){
    node_t * new_n = ( node_t * ) malloc( sizeof( node_t ) );
    new_n->parent = parent;
    new_n->depth = parent->depth + 1;
    copy_state( init_data, &( new_n->state ), &( parent->state ) );
    return new_n;
}

/**
 * Apply an action to node n, create a new node resulting from
 * executing the action, and return if the player moved
*/
bool applyAction( sokoban_t* init_data, node_t* n,
                 node_t** new_node, move_t action ){

    bool player_moved = false;

    *new_node = create_node( init_data, n );
    ( *new_node )->move = action;
    ( *new_node )->priority =  -( *new_node )->depth;

    player_moved =
    execute_move_t( init_data, &( ( *new_node )->state), action );

    return player_moved;

}

/**
 * Book keeping variable and function to free memory once the solver finishes
*/

//Line 4 of the pseudocode:
node_t** expanded_nodes_table;
unsigned expanded_nodes_table_size = 10000000; //10M

void update_explore_table(node_t* n, unsigned expanded_nodes ){
    if( expanded_nodes > expanded_nodes_table_size - 1){
    expanded_nodes_table_size *= 2;
    expanded_nodes_table = realloc(expanded_nodes_table,
                                   sizeof(node_t*) * expanded_nodes_table_size);
    }
    
    expanded_nodes_table[ expanded_nodes ] = n;

}

/*This function was altered to free every part of the expanded nodes table,
 and makes the memory freeing process more convenient
 */
void free_memory( unsigned expanded_nodes, sokoban_t *init_data ){
    for( unsigned i = 1; i <= expanded_nodes; i++ ){
        for( int j = 0; j<init_data->lines; j++ ){
            free( expanded_nodes_table[i]->state.map[j] );
        }
        free( expanded_nodes_table[i]->state.map );
        free( expanded_nodes_table[i] );
    }
    free( expanded_nodes_table );
}


/**
 * Given a 2D map, returns a 1D map
*/
void flatten_map( sokoban_t* init_data, char **dst_map, char **src_map ){

    int current_i = 0;
    for ( int i = 0; i < init_data->lines; ++i )
    {
        int width = strlen( src_map[i] );
        for ( int j = 0; j < width; j++ ){
            (*dst_map)[current_i]  = src_map[i][j];
            current_i++;
        }
    }
}

/**
 * Find a solution by exploring all possible paths
 */
void find_solution(sokoban_t* init_data, bool show_solution)
{
    // Keep track of solving time
    clock_t start = clock();
    
    // Solution String containing the sequence of moves
    char* solution = NULL;

    HashTable hashTable;
    struct heap pq;

    // Statistics
    unsigned generated_nodes = 0;
    unsigned expanded_nodes = 0;
    unsigned duplicated_nodes = 0;
    int max_depth = 0;
    unsigned solution_size = 0;

    // Choose initial capacity of PRIME NUMBER
    // Specify the size of the keys and values you want to store once
    // The Hash Table only accept a 1D key and value.
    
    ht_setup( &hashTable, sizeof(int8_t) * init_data->num_chars_map,
             sizeof(int8_t) * init_data->num_chars_map, 16769023);

    

    // Data structure to create a 1D representation of the map
    // Needed to interact with the hash table
    char* flat_map = calloc( init_data->num_chars_map, sizeof ( char ) );

    // Initialize heap
    heap_init( &pq) ;

    // Initialize expanded nodes table.
    // This table will be used to free your memory once a solution is found
    expanded_nodes_table =
    ( node_t** ) malloc( sizeof( node_t* ) * expanded_nodes_table_size );
    

    // Add the initial node: line 2 of the pseudocode
    node_t* n = create_init_node( init_data );
    
    // Use the max heap API provided in priority_queue.h
    heap_push(&pq,n);
    
    /**
     * FILL IN THE GRAPH ALGORITHM
     * This section of the code works through line 6 onwards of the pseucode.
     * */
    
    //This while loop covers lines 6 to 31 of the pseudocode
    while( pq.count != 0 ){
        
        //This block covers lines 7 to 9 of the pseudocode
        node_t *n = heap_delete( &pq );
        expanded_nodes += 1;
        update_explore_table( n, expanded_nodes );
        
        //This block covers lines 10 to 14 of the pseudocode
        if( winning_condition( init_data, &( n->state ) ) ){
            solution = save_solution(n);
            solution_size = n->depth;
            break;
        }
        
        move_t *action_move = NULL;
        
        //This for loop covers lines 15 to 30 of the pseudocode
        for( move_t move = 0; move <4; move++ ){
            action_move = &move;
            node_t *new_node = NULL;
            
            //Lines 16 and 17 of the pseudocode
            bool player_moved =
            applyAction( init_data, n, &new_node, *action_move );
            generated_nodes += 1;
            
            //Lines 18 to 21 of the pseudocode
            if( !player_moved ||
               simple_corner_deadlock(init_data, &( new_node->state ) ) ) {
                for( int i = 0; i < init_data->lines; i++ ) {
                    free( new_node->state.map[i] );
                }
                free( new_node->state.map );
                free( new_node );
                continue;
            }
            
            //Lines 22 to 25 of the pseudocode
            flatten_map( init_data, &flat_map, new_node->state.map );
            if( ht_contains( &hashTable, flat_map ) ) {
                duplicated_nodes += 1;
                for( int i = 0; i< init_data->lines; i++ ) {
                    free( new_node->state.map[i] );
                }
                free( new_node->state.map );
                free( new_node );
                continue;
            }
            
            //Lines 28 and 29 of the pseudocode
            ht_insert( &hashTable,flat_map, flat_map );
            heap_push( &pq, new_node );
        }
    }
    //End of implementing pseudocode from provided algorithm
    
    //----------------------------
    
    // Free Memory of HashTable and flatmap
    ht_clear(&hashTable);
    ht_destroy(&hashTable);
    free(flat_map);
    //----------------------------

    // Stop clock
    clock_t end = clock();
    double cpu_time_used = ( ( double ) ( end - start ) ) / CLOCKS_PER_SEC;

    // Show Soltion
    if( show_solution && solution != NULL )
        play_solution( *init_data, solution );

    endwin();

    if( solution != NULL ){
        printf("\nSOLUTION:                               \n");
        printf( "%s\n\n", solution);
        FILE *fptr = fopen("solution.txt", "w");
        if (fptr == NULL)
        {
            printf("Could not open file");
            return ;
        }
        fprintf(fptr,"%s\n", solution);
        fclose(fptr);
        
        free(solution);
    }


    printf("STATS: \n");
    printf("\tExpanded nodes: %'d\n\tGenerated nodes: %'d\n\tDuplicated nodes:
           %'d\n", expanded_nodes, generated_nodes, duplicated_nodes);
    printf("\tSolution Length: %d\n", solution_size);
    printf("\tExpanded/seconds: %d\n", (int)(expanded_nodes/cpu_time_used) );
    printf("\tTime (seconds): %f\n", cpu_time_used );
    
    //----------------------------
    /*The following lines free any existing memory from the:
     * 1. Explored nodes table
     * 2. Priority Queue
     * 3. Heap Array
     *
     * The free_memory function is moved to this part, as the printing solutions
     * section requires the data in the expanded_nodes_table.
     */
           
    free_memory( expanded_nodes, init_data );

    for( int i = 0; i < pq.count; i++ ){
        //node_t *free_node = heap_delete(&pq);
        for( int j = 0; j<init_data->lines; j++ ){
            free( pq.heaparr[i]->state.map[j] );
        }
        free(pq.heaparr[i]->state.map);
    }
           
    emptyPQ( &pq );
    free( pq.heaparr );
    
    free( init_data->buffer );
    for( int i = 0; i < init_data->lines; i++ ){
        free( init_data->map[i] );
        free( init_data->map_save[i] );
    }
    free( init_data->map );
    free( init_data->map_save );
           
    //----------------------------
}

void solve(char const *path, bool show_solution)
{
    /**
     * Load Map
    */
    sokoban_t sokoban = make_map(path, sokoban);
    
    /**
     * Count number of boxes and Storage locations
    */
    map_check(sokoban);

    /**
     * Locate player x,y position
    */
    sokoban = find_player(sokoban);
    
    sokoban.base_path = path;

    find_solution(&sokoban, show_solution);
}

