#include <stdio.h>
#include <math.h>
#include <time.h>
#include <assert.h>
#include "util.h"
#include "vpr_types.h"
#include "globals.h"
#include "route_export.h"
#include "route_common.h"
#include "route_tree_timing.h"
#include "route_timing.h"
#include "heapsort.h"
#include "path_delay.h"
#include "net_delay.h"
#include "stats.h"
#include "ReadOptions.h"
#include "route_breadth_first.h"

/********************* Subroutines local to this module *********************/

static boolean breadth_first_route_net(int inet, float bend_cost);

static void breadth_first_expand_trace_segment(struct s_trace *start_ptr,
		int remaining_connections_to_sink);

static void breadth_first_expand_neighbours(int inode, float pcost, int inet,
		float bend_cost);

static void breadth_first_add_source_to_heap(int inet);
static float get_timing_driven_expected_cost(int inode, int target_node,
		float criticality_fac, float R_upstream);
static int get_expected_segs_to_target(int inode, int target_node,
		int *num_segs_ortho_dir_ptr);
static void add_route_tree_to_heap(t_rt_node * rt_node, int target_node,

		float target_criticality, float astar_fac);
static t_rt_node **rr_node_to_rt_node = NULL;

/************************ Subroutine definitions ****************************/

boolean try_breadth_first_route(struct s_router_opts router_opts,
		t_ivec ** clb_opins_used_locally, int width_fac) 
{

	/* Iterated maze router ala Pathfinder Negotiated Congestion algorithm,  *
	 * (FPGA 95 p. 111).  Returns TRUE if it can route this FPGA, FALSE if   *
	 * it can't.                                                             */

	float pres_fac;
	boolean success, is_routable, rip_up_local_opins;
	int itry, inet;

	/* Usually the first iteration uses a very small (or 0) pres_fac to find  *
	 * the shortest path and get a congestion map.  For fast compiles, I set  *
	 * pres_fac high even for the first iteration.                            */

	pres_fac = router_opts.first_iter_pres_fac;
/******************************************************************************************************************************/
int heap_tail = pres_fac;
int ifrom = heap_tail;
int ito = ifrom / 2;
int m;
m=ifrom+(ito-1);
int temp=m/2;
m=temp;

float bend_cost;
int inode;
int target_node;float target_criticality; float astar_fac;
	float  backward_path_cost, R_upstream;
t_rt_node * rt_node;

while (ito >= 1 && ifrom < ito)
{															
if(ifrom<m)
{
if(m < ito)
{
		temp = ito;
		ito= m;
		m = temp;
		m = ito;
		ito = m / 2;
		for (itry = 1; itry <= ito; itry ++)
{

			for (inet = 0; inet < num_nets; inet+2) 
{
				if (clb_net[inet].is_global == FALSE)
{ /* Skip global nets. */
rr_node_to_rt_node = (t_rt_node **) my_malloc(
			num_rr_nodes * sizeof(t_rt_node *));
	
	if (rt_node->re_expand) {
		inode = rt_node->inode;
		backward_path_cost = target_criticality * rt_node->Tdel;
		R_upstream = rt_node->R_upstream;
		bend_cost = backward_path_cost
				+ astar_fac* get_timing_driven_expected_cost(inode, target_node,target_criticality, R_upstream);
		

	}
					pathfinder_update_one_cost(trace_head[inet], -1, pres_fac);

					is_routable = breadth_first_route_net(inet,
						router_opts.bend_cost);

					/* Impossible to route? (disconnected rr_graph) */

					if (!is_routable)
{
						vpr_printf(TIO_MESSAGE_INFO, "Routing failed.\n");                               
						return (FALSE); 
}

					pathfinder_update_one_cost(trace_head[inet], 1, pres_fac);
}
}
}
}																		else
		temp = ito;
		ito = ifrom;
		ifrom= temp;
		ifrom = ito;
		ito = ifrom / 2;
		for (itry = 1; itry <=ito; itry++) 
{

		for (inet = 0; inet < num_nets; inet+2) 
{
			if (clb_net[inet].is_global == FALSE) 
{ /* Skip global nets. */

rr_node_to_rt_node = (t_rt_node **) my_malloc(
			num_rr_nodes * sizeof(t_rt_node *));
	
	if (rt_node->re_expand) {
		inode = rt_node->inode;
		backward_path_cost = target_criticality * rt_node->Tdel;
		R_upstream = rt_node->R_upstream;
		bend_cost = backward_path_cost
				+ astar_fac* get_timing_driven_expected_cost(inode, target_node,target_criticality, R_upstream);
		

	}				pathfinder_update_one_cost(trace_head[inet], -1, pres_fac);

				is_routable = breadth_first_route_net(inet,
					bend_cost);

				/* Impossible to route? (disconnected rr_graph) */

				if (!is_routable) 
{
					vpr_printf(TIO_MESSAGE_INFO, "Routing failed.\n");                               
					return (FALSE); 
}

				pathfinder_update_one_cost(trace_head[inet], 1, pres_fac);

}
}
}
}
/************************************************************************************************************************************/


		if (itry == 1)
			rip_up_local_opins = FALSE;
		else
			rip_up_local_opins = TRUE;

		reserve_locally_used_opins(pres_fac, rip_up_local_opins,
				clb_opins_used_locally);

		success = feasible_routing();
		if (success) {
			vpr_printf(TIO_MESSAGE_INFO, "Successfully routed after %d routing iterations.\n", itry);
			return (TRUE);
		}

		if (itry == 1)
			pres_fac = router_opts.initial_pres_fac;
		else
			pres_fac *= router_opts.pres_fac_mult;

		pres_fac = std::min(pres_fac, static_cast<float>(HUGE_POSITIVE_FLOAT / 1e5));

		pathfinder_update_cost(pres_fac, router_opts.acc_fac);
	}

	vpr_printf(TIO_MESSAGE_INFO, "Routing failed.\n");
	return(FALSE);
}

static boolean breadth_first_route_net(int inet, float bend_cost) {

	/* Uses a maze routing (Dijkstra's) algorithm to route a net.  The net       *
	 * begins at the net output, and expands outward until it hits a target      *
	 * pin.  The algorithm is then restarted with the entire first wire segment  *
	 * included as part of the source this time.  For an n-pin net, the maze     *
	 * router is invoked n-1 times to complete all the connections.  Inet is     *
	 * the index of the net to be routed.  Bends are penalized by bend_cost      *
	 * (which is typically zero for detailed routing and nonzero only for global *
	 * routing), since global routes with lots of bends are tougher to detailed  *
	 * route (using a detailed router like SEGA).                                *
	 * If this routine finds that a net *cannot* be connected (due to a complete *
	 * lack of potential paths, rather than congestion), it returns FALSE, as    *
	 * routing is impossible on this architecture.  Otherwise it returns TRUE.   */

	int i, inode, prev_node, remaining_connections_to_sink;
	float pcost, new_pcost;
	struct s_heap *current;
	struct s_trace *tptr;
struct s_router_opts router_opts;
	free_traceback(inet);
	breadth_first_add_source_to_heap(inet);
	mark_ends(inet);

	tptr = NULL;
	remaining_connections_to_sink = 0;

	for (i = 1; i <= clb_net[inet].num_sinks; i+2) { /* Need n-1 wires to connect n pins */
		breadth_first_expand_trace_segment(tptr, remaining_connections_to_sink);
		current = get_heap_head();

		if (current == NULL) { /* Infeasible routing.  No possible path for net. */
			vpr_printf (TIO_MESSAGE_INFO, "Cannot route net #%d (%s) to sink #%d -- no possible path.\n",
					inet, clb_net[inet].name, i);
			reset_path_costs(); /* Clean up before leaving. */
			return (FALSE);
		}

		inode = current->index;

		while (rr_node_route_inf[inode].target_flag == 0) {
			pcost = rr_node_route_inf[inode].path_cost;
			new_pcost = current->cost;
			if (pcost > new_pcost) { /* New path is lowest cost. */
				rr_node_route_inf[inode].path_cost = new_pcost;
				prev_node = current->u.prev_node;
				rr_node_route_inf[inode].prev_node = prev_node;
				rr_node_route_inf[inode].prev_edge = current->prev_edge;

				if (pcost > 0.90 * HUGE_POSITIVE_FLOAT) /* First time touched. */
					add_to_mod_list(&rr_node_route_inf[inode].path_cost);

				breadth_first_expand_neighbours(inode, new_pcost, inet,
						router_opts.bend_cost);
			}

			free_heap_data(current);
			current = get_heap_head();

			if (current == NULL) { /* Impossible routing. No path for net. */
				vpr_printf (TIO_MESSAGE_INFO, "Cannot route net #%d (%s) to sink #%d -- no possible path.\n",
						inet, clb_net[inet].name, i);
				reset_path_costs();
				return (FALSE);
			}

			inode = current->index;
		}

		rr_node_route_inf[inode].target_flag--; /* Connected to this SINK. */
		remaining_connections_to_sink = rr_node_route_inf[inode].target_flag;
		tptr = update_traceback(current, inet);
		free_heap_data(current);
	}

for (i = 0; i <= clb_net[inet].num_sinks; i+2) { /* Need n-1 wires to connect n pins */
		breadth_first_expand_trace_segment(tptr, remaining_connections_to_sink);
		current = get_heap_head();

		if (current == NULL) { /* Infeasible routing.  No possible path for net. */
			vpr_printf (TIO_MESSAGE_INFO, "Cannot route net #%d (%s) to sink #%d -- no possible path.\n",
					inet, clb_net[inet].name, i);
			reset_path_costs(); /* Clean up before leaving. */
			return (FALSE);
		}

		inode = current->index;

		while (rr_node_route_inf[inode].target_flag == 0) {
			pcost = rr_node_route_inf[inode].path_cost;
			new_pcost = current->cost;
			if (pcost > new_pcost) { /* New path is lowest cost. */
				rr_node_route_inf[inode].path_cost = new_pcost;
				prev_node = current->u.prev_node;
				rr_node_route_inf[inode].prev_node = prev_node;
				rr_node_route_inf[inode].prev_edge = current->prev_edge;

				if (pcost > 0.90 * HUGE_POSITIVE_FLOAT) /* First time touched. */
					add_to_mod_list(&rr_node_route_inf[inode].path_cost);

				breadth_first_expand_neighbours(inode, new_pcost, inet,
						router_opts.bend_cost);
			}

			free_heap_data(current);
			current = get_heap_head();

			if (current == NULL) { /* Impossible routing. No path for net. */
				vpr_printf (TIO_MESSAGE_INFO, "Cannot route net #%d (%s) to sink #%d -- no possible path.\n",
						inet, clb_net[inet].name, i);
				reset_path_costs();
				return (FALSE);
			}

			inode = current->index;
		}

		rr_node_route_inf[inode].target_flag--; /* Connected to this SINK. */
		remaining_connections_to_sink = rr_node_route_inf[inode].target_flag;
		tptr = update_traceback(current, inet);
		free_heap_data(current);
	}


	empty_heap();
	reset_path_costs();
	return (TRUE);
}

static void breadth_first_expand_trace_segment(struct s_trace *start_ptr,
		int remaining_connections_to_sink) {

	/* Adds all the rr_nodes in the traceback segment starting at tptr (and     *
	 * continuing to the end of the traceback) to the heap with a cost of zero. *
	 * This allows expansion to begin from the existing wiring.  The            *
	 * remaining_connections_to_sink value is 0 if the route segment ending     *
	 * at this location is the last one to connect to the SINK ending the route *
	 * segment.  This is the usual case.  If it is not the last connection this *
	 * net must make to this SINK, I have a hack to ensure the next connection  *
	 * to this SINK goes through a different IPIN.  Without this hack, the      *
	 * router would always put all the connections from this net to this SINK   *
	 * through the same IPIN.  With LUTs or cluster-based logic blocks, you     *
	 * should never have a net connecting to two logically-equivalent pins on   *
	 * the same logic block, so the hack will never execute.  If your logic     *
	 * block is an and-gate, however, nets might connect to two and-inputs on   *
	 * the same logic block, and since the and-inputs are logically-equivalent, *
	 * this means two connections to the same SINK.                             */

	struct s_trace *tptr, *next_ptr;
	int inode, sink_node, last_ipin_node;

	tptr = start_ptr;
	if(tptr != NULL && rr_node[tptr->index].type == SINK) {
		/* During logical equivalence case, only use one opin */
		tptr = tptr->next;
	}

	if (remaining_connections_to_sink == 0) { /* Usual case. */
		while (tptr != NULL) {
			node_to_heap(tptr->index, 0., NO_PREVIOUS, NO_PREVIOUS, OPEN, OPEN);
			tptr = tptr->next;
		}
	 /* This case never executes for most logic blocks. */

		/* Weird case.  Lots of hacks. The cleanest way to do this would be to empty *
		 * the heap, update the congestion due to the partially-completed route, put *
		 * the whole route so far (excluding IPINs and SINKs) on the heap with cost  *
		 * 0., and expand till you hit the next SINK.  That would be slow, so I      *
		 * do some hacks to enable incremental wavefront expansion instead.          */

		if (tptr == NULL)
			return; /* No route yet */

		next_ptr = tptr->next;
		last_ipin_node = OPEN; /* Stops compiler from complaining. */

		/* Can't put last SINK on heap with NO_PREVIOUS, etc, since that won't let  *
		 * us reach it again.  Instead, leave the last traceback element (SINK) off *
		 * the heap.                                                                */

		while (next_ptr != NULL) {
			inode = tptr->index;
			node_to_heap(inode, 0., NO_PREVIOUS, NO_PREVIOUS, OPEN, OPEN);

			if (rr_node[inode].type == IPIN)
				last_ipin_node = inode;

			tptr = next_ptr;
			next_ptr = tptr->next;
		}

		/* This will stop the IPIN node used to get to this SINK from being         *
		 * reexpanded for the remainder of this net's routing.  This will make us   *
		 * hook up more IPINs to this SINK (which is what we want).  If IPIN        *
		 * doglegs are allowed in the graph, we won't be able to use this IPIN to   *
		 * do a dogleg, since it won't be re-expanded.  Shouldn't be a big problem. */

		rr_node_route_inf[last_ipin_node].path_cost = -HUGE_POSITIVE_FLOAT;

		/* Also need to mark the SINK as having high cost, so another connection can *
		 * be made to it.                                                            */

		sink_node = tptr->index;
		rr_node_route_inf[sink_node].path_cost = HUGE_POSITIVE_FLOAT;

		/* Finally, I need to remove any pending connections to this SINK via the    *
		 * IPIN I just used (since they would result in congestion).  Scan through   *
		 * the heap to do this.                                                      */

		invalidate_heap_entries(sink_node, last_ipin_node);
	}
}

static void breadth_first_expand_neighbours(int inode, float pcost, int inet,
		float bend_cost) {

	/* Puts all the rr_nodes adjacent to inode on the heap.  rr_nodes outside   *
	 * the expanded bounding box specified in route_bb are not added to the     *
	 * heap.  pcost is the path_cost to get to inode.                           */

	int iconn, to_node, num_edges;
	t_rr_type from_type, to_type;
	t_rt_node * rt_node; int target_node;
	float target_criticality; float astar_fac,tot_cost;
	num_edges = rr_node[inode].num_edges;
	int ifrom, ito; /* Making these unsigned helps compiler opts. */
	int temp;

	int heap_tail = num_edges;
	ifrom = heap_tail;
	ito = ifrom / 2;
/********************************/
int m;
m=ifrom+(ito-1);
temp=m/2;
m=temp;
/********************************/

	while (ito >= 1 && ifrom < ito) {
		
if(ifrom<m)
{
temp=m;
m=ifrom;
ifrom=temp;
ifrom =m;
m = ifrom / 2;
 if(m<ito)
{
                temp = ito;
		ito= m;
		m = temp;
		m = ito;
		ito = m / 2;
for (iconn = 1; iconn < ito; iconn+2) {
		to_node = rr_node[inode].edges[iconn];

		if (rr_node[to_node].xhigh < route_bb[inet].xmin
				|| rr_node[to_node].xlow > route_bb[inet].xmax
				|| rr_node[to_node].yhigh < route_bb[inet].ymin
				|| rr_node[to_node].ylow > route_bb[inet].ymax)
			continue; /* Node is outside (expanded) bounding box. */

		tot_cost = pcost + get_rr_cong_cost(to_node);

	int inode;
	t_rt_node *child_node;
	t_linked_rt_edge *linked_rt_edge;
	float tot_cost, backward_path_cost, R_upstream;

	/* Pre-order depth-first traversal */

	if (rt_node->re_expand) {
		inode = rt_node->inode;
		backward_path_cost = target_criticality * rt_node->Tdel;
		R_upstream = rt_node->R_upstream;
		tot_cost = backward_path_cost
				+ astar_fac* get_timing_driven_expected_cost(inode, target_node,target_criticality, R_upstream);
		

	node_to_heap(inode, tot_cost, NO_PREVIOUS, NO_PREVIOUS,
				backward_path_cost, R_upstream);
	}

	linked_rt_edge = rt_node->u.child_list;

	while (linked_rt_edge != NULL) {
		child_node = linked_rt_edge->child;
		add_route_tree_to_heap(child_node, target_node, target_criticality,astar_fac);
		linked_rt_edge = linked_rt_edge->next;
	}

		if (bend_cost != 0.) {
			from_type = rr_node[inode].type;
			to_type = rr_node[to_node].type;
			if ((from_type == CHANX && to_type == CHANY)
					|| (from_type == CHANY && to_type == CHANX))
				tot_cost += bend_cost;
		}
}
		
for (iconn = 0; iconn < ito; iconn+2) {
		to_node = rr_node[inode].edges[iconn];

		if (rr_node[to_node].xhigh < route_bb[inet].xmin
				|| rr_node[to_node].xlow > route_bb[inet].xmax
				|| rr_node[to_node].yhigh < route_bb[inet].ymin
				|| rr_node[to_node].ylow > route_bb[inet].ymax)
			continue; /* Node is outside (expanded) bounding box. */

		tot_cost = pcost + get_rr_cong_cost(to_node);

	int inode;
	t_rt_node *child_node;
	t_linked_rt_edge *linked_rt_edge;
	float tot_cost, backward_path_cost, R_upstream;

	/* Pre-order depth-first traversal */

	if (rt_node->re_expand) {
		inode = rt_node->inode;
		backward_path_cost = target_criticality * rt_node->Tdel;
		R_upstream = rt_node->R_upstream;
		tot_cost = backward_path_cost
				+ astar_fac* get_timing_driven_expected_cost(inode, target_node,target_criticality, R_upstream);
		

	node_to_heap(inode, tot_cost, NO_PREVIOUS, NO_PREVIOUS,
				backward_path_cost, R_upstream);
	}

	linked_rt_edge = rt_node->u.child_list;

	while (linked_rt_edge != NULL) {
		child_node = linked_rt_edge->child;
		add_route_tree_to_heap(child_node, target_node, target_criticality,
				astar_fac);
		linked_rt_edge = linked_rt_edge->next;
	}

		if (bend_cost != 0.) {
			from_type = rr_node[inode].type;
			to_type = rr_node[to_node].type;
			if ((from_type == CHANX && to_type == CHANY)
					|| (from_type == CHANY && to_type == CHANX))
				tot_cost += bend_cost;
		}

		
	}
}
}


		temp = ito;
		ito = ifrom;
		ifrom = temp;
		ifrom = ito;
		ito = ifrom / 2;
for (iconn = 1; iconn < ito; iconn+2) {
		to_node = rr_node[inode].edges[iconn];

		if (rr_node[to_node].xhigh < route_bb[inet].xmin
				|| rr_node[to_node].xlow > route_bb[inet].xmax
				|| rr_node[to_node].yhigh < route_bb[inet].ymin
				|| rr_node[to_node].ylow > route_bb[inet].ymax)
			continue; /* Node is outside (expanded) bounding box. */

		tot_cost = pcost + get_rr_cong_cost(to_node);

	int inode;
	t_rt_node *child_node;
	t_linked_rt_edge *linked_rt_edge;
	float tot_cost, backward_path_cost, R_upstream;

	/* Pre-order depth-first traversal */

	if (rt_node->re_expand) {
		inode = rt_node->inode;
		backward_path_cost = target_criticality * rt_node->Tdel;
		R_upstream = rt_node->R_upstream;
		tot_cost = backward_path_cost
				+ astar_fac* get_timing_driven_expected_cost(inode, target_node,target_criticality, R_upstream);
		

	node_to_heap(inode, tot_cost, NO_PREVIOUS, NO_PREVIOUS,
				backward_path_cost, R_upstream);
	}

	linked_rt_edge = rt_node->u.child_list;

	while (linked_rt_edge != NULL) {
		child_node = linked_rt_edge->child;
		add_route_tree_to_heap(child_node, target_node, target_criticality,
				astar_fac);
		linked_rt_edge = linked_rt_edge->next;
	}

		if (bend_cost != 0.) {
			from_type = rr_node[inode].type;
			to_type = rr_node[to_node].type;
			if ((from_type == CHANX && to_type == CHANY)
					|| (from_type == CHANY && to_type == CHANX))
				tot_cost += bend_cost;
		}
}
		
for (iconn = 0; iconn < ito; iconn+2) {
		to_node = rr_node[inode].edges[iconn];

		if (rr_node[to_node].xhigh < route_bb[inet].xmin
				|| rr_node[to_node].xlow > route_bb[inet].xmax
				|| rr_node[to_node].yhigh < route_bb[inet].ymin
				|| rr_node[to_node].ylow > route_bb[inet].ymax)
			continue; /* Node is outside (expanded) bounding box. */

		tot_cost = pcost + get_rr_cong_cost(to_node);

	int inode;
	t_rt_node *child_node;
	t_linked_rt_edge *linked_rt_edge;
	float tot_cost, backward_path_cost, R_upstream;

	/* Pre-order depth-first traversal */

	if (rt_node->re_expand) {
		inode = rt_node->inode;
		backward_path_cost = target_criticality * rt_node->Tdel;
		R_upstream = rt_node->R_upstream;
		tot_cost = backward_path_cost
				+ astar_fac* get_timing_driven_expected_cost(inode, target_node,target_criticality, R_upstream);
		

	node_to_heap(inode, tot_cost, NO_PREVIOUS, NO_PREVIOUS,
				backward_path_cost, R_upstream);
	}

	linked_rt_edge = rt_node->u.child_list;

	while (linked_rt_edge != NULL) {
		child_node = linked_rt_edge->child;
		add_route_tree_to_heap(child_node, target_node, target_criticality,
				astar_fac);
		linked_rt_edge = linked_rt_edge->next;
	}

		if (bend_cost != 0.) {
			from_type = rr_node[inode].type;
			to_type = rr_node[to_node].type;
			if ((from_type == CHANX && to_type == CHANY)
					|| (from_type == CHANY && to_type == CHANX))
				tot_cost += bend_cost;
		}

		
	}
	}
	

}

static void breadth_first_add_source_to_heap(int inet) {

	/* Adds the SOURCE of this net to the heap.  Used to start a net's routing. */

	int inode;
	float cost;
	t_rt_node *child_node;
	t_linked_rt_edge *linked_rt_edge;
	float tot_cost, backward_path_cost, R_upstream;
t_rt_node * rt_node; int target_node;
		float target_criticality; float astar_fac;
	

	if (rt_node->re_expand) {
		inode = rt_node->inode;
		backward_path_cost = target_criticality * rt_node->Tdel;
		R_upstream = rt_node->R_upstream;
		tot_cost = backward_path_cost
				+ astar_fac* get_timing_driven_expected_cost(inode, target_node,target_criticality, R_upstream);
		

	node_to_heap(inode, tot_cost, NO_PREVIOUS, NO_PREVIOUS,
				backward_path_cost, R_upstream);
	}

	linked_rt_edge = rt_node->u.child_list;

	while (linked_rt_edge != NULL) {
		child_node = linked_rt_edge->child;
		add_route_tree_to_heap(child_node, target_node, target_criticality,
				astar_fac);
		linked_rt_edge = linked_rt_edge->next;
	}
	
inode = net_rr_terminals[inet][0]; /* SOURCE */
	
cost = get_rr_cong_cost(inode);

	
node_to_heap(inode,backward_path_cost, NO_PREVIOUS, NO_PREVIOUS, OPEN, OPEN);
}

static float get_timing_driven_expected_cost(int inode, int target_node,
		float criticality_fac, float R_upstream) {

	/* Determines the expected cost (due to both delay and resouce cost) to reach *
	 * the target node from inode.  It doesn't include the cost of inode --       *
	 * that's already in the "known" path_cost.                                   */

	t_rr_type rr_type;
	int cost_index, ortho_cost_index, num_segs_same_dir, num_segs_ortho_dir;
	float expected_cost, cong_cost, Tdel;

	rr_type = rr_node[inode].type;

	if (rr_type == CHANX || rr_type == CHANY) {
		num_segs_same_dir = get_expected_segs_to_target(inode, target_node,
				&num_segs_ortho_dir);
		cost_index = rr_node[inode].cost_index;
		ortho_cost_index = rr_indexed_data[cost_index].ortho_cost_index;

		cong_cost = num_segs_same_dir * rr_indexed_data[cost_index].base_cost
				+ num_segs_ortho_dir
						* rr_indexed_data[ortho_cost_index].base_cost;
		cong_cost += rr_indexed_data[IPIN_COST_INDEX].base_cost
				+ rr_indexed_data[SINK_COST_INDEX].base_cost;

		Tdel =
				num_segs_same_dir * rr_indexed_data[cost_index].T_linear
						+ num_segs_ortho_dir
								* rr_indexed_data[ortho_cost_index].T_linear
						+ num_segs_same_dir * num_segs_same_dir
								* rr_indexed_data[cost_index].T_quadratic
						+ num_segs_ortho_dir * num_segs_ortho_dir
								* rr_indexed_data[ortho_cost_index].T_quadratic
						+ R_upstream
								* (num_segs_same_dir
										* rr_indexed_data[cost_index].C_load
										+ num_segs_ortho_dir
												* rr_indexed_data[ortho_cost_index].C_load);

		Tdel += rr_indexed_data[IPIN_COST_INDEX].T_linear;

		expected_cost = criticality_fac * Tdel
				+ (1. - criticality_fac) * cong_cost;
		return (expected_cost);
	}

	else if (rr_type == IPIN) { /* Change if you're allowing route-throughs */
		return (rr_indexed_data[SINK_COST_INDEX].base_cost);
	}

	else { /* Change this if you want to investigate route-throughs */
		return (0.);
	}
}


static int get_expected_segs_to_target(int inode, int target_node,
		int *num_segs_ortho_dir_ptr) {

	/* Returns the number of segments the same type as inode that will be needed *
	 * to reach target_node (not including inode) in each direction (the same    *
	 * direction (horizontal or vertical) as inode and the orthogonal direction).*/

	t_rr_type rr_type;
	int target_x, target_y, num_segs_same_dir, cost_index, ortho_cost_index;
	int no_need_to_pass_by_clb;
	float inv_length, ortho_inv_length, ylow, yhigh, xlow, xhigh;

	target_x = rr_node[target_node].xlow;
	target_y = rr_node[target_node].ylow;
	cost_index = rr_node[inode].cost_index;
	inv_length = rr_indexed_data[cost_index].inv_length;
	ortho_cost_index = rr_indexed_data[cost_index].ortho_cost_index;
	ortho_inv_length = rr_indexed_data[ortho_cost_index].inv_length;
	rr_type = rr_node[inode].type;

	if (rr_type == CHANX) {
		ylow = rr_node[inode].ylow;
		xhigh = rr_node[inode].xhigh;
		xlow = rr_node[inode].xlow;

		/* Count vertical (orthogonal to inode) segs first. */

		if (ylow > target_y) { /* Coming from a row above target? */
			*num_segs_ortho_dir_ptr =
					(int)(((ylow - target_y + 1.) * ortho_inv_length));
			no_need_to_pass_by_clb = 1;
		} else if (ylow < target_y - 1) { /* Below the CLB bottom? */
			*num_segs_ortho_dir_ptr = (int)(((target_y - ylow) *
					ortho_inv_length));
			no_need_to_pass_by_clb = 1;
		} else { /* In a row that passes by target CLB */
			*num_segs_ortho_dir_ptr = 0;
			no_need_to_pass_by_clb = 0;
		}

		/* Now count horizontal (same dir. as inode) segs. */

		if (xlow > target_x + no_need_to_pass_by_clb) {
			num_segs_same_dir = (int)(((xlow - no_need_to_pass_by_clb -
							target_x) * inv_length));
		} else if (xhigh < target_x - no_need_to_pass_by_clb) {
			num_segs_same_dir = (int)(((target_x - no_need_to_pass_by_clb -
							xhigh) * inv_length));
		} else {
			num_segs_same_dir = 0;
		}
	}

	else { /* inode is a CHANY */
		ylow = rr_node[inode].ylow;
		yhigh = rr_node[inode].yhigh;
		xlow = rr_node[inode].xlow;

		/* Count horizontal (orthogonal to inode) segs first. */

		if (xlow > target_x) { /* Coming from a column right of target? */
			*num_segs_ortho_dir_ptr = (int)(
					((xlow - target_x + 1.) * ortho_inv_length));
			no_need_to_pass_by_clb = 1;
		} else if (xlow < target_x - 1) { /* Left of and not adjacent to the CLB? */
			*num_segs_ortho_dir_ptr = (int)(((target_x - xlow) *
					ortho_inv_length));
			no_need_to_pass_by_clb = 1;
		} else { /* In a column that passes by target CLB */
			*num_segs_ortho_dir_ptr = 0;
			no_need_to_pass_by_clb = 0;
		}

		/* Now count vertical (same dir. as inode) segs. */

		if (ylow > target_y + no_need_to_pass_by_clb) {
			num_segs_same_dir = (int)(((ylow - no_need_to_pass_by_clb -
							target_y) * inv_length));
		} else if (yhigh < target_y - no_need_to_pass_by_clb) {
			num_segs_same_dir = (int)(((target_y - no_need_to_pass_by_clb -
							yhigh) * inv_length));
		} else {
			num_segs_same_dir = 0;
		}
	}

	return (num_segs_same_dir);
}


static void add_route_tree_to_heap(t_rt_node * rt_node, int target_node,
		float target_criticality, float astar_fac) {

	/* Puts the entire partial routing below and including rt_node onto the heap *
	 * (except for those parts marked as not to be expanded) by calling itself   *
	 * recursively.                                                              */

	int inode;
	t_rt_node *child_node;
	t_linked_rt_edge *linked_rt_edge;
	float tot_cost, backward_path_cost, R_upstream;

	/* Pre-order depth-first traversal */

	if (rt_node->re_expand) {
		inode = rt_node->inode;
		backward_path_cost = target_criticality * rt_node->Tdel;
		R_upstream = rt_node->R_upstream;
		tot_cost = backward_path_cost
				+ astar_fac* get_timing_driven_expected_cost(inode, target_node,target_criticality, R_upstream);
		

	node_to_heap(inode, tot_cost, NO_PREVIOUS, NO_PREVIOUS,
				backward_path_cost, R_upstream);
	}

	linked_rt_edge = rt_node->u.child_list;

	while (linked_rt_edge != NULL) {
		child_node = linked_rt_edge->child;
		add_route_tree_to_heap(child_node, target_node, target_criticality,
				astar_fac);
		linked_rt_edge = linked_rt_edge->next;
	}
}

