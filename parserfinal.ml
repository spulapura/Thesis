(*
 * Roshan Pulapura
 * Computer Science 91R
 * August 2020 
*)

type node = string;;


(*Each tree is either a leaf node or a node with a list of children*)
type tree = 
	|Leaf of node
	|Tree of node * tree list;;

(*Returns phrasal/lexical token at the top of tree (head)*)
let get_head (t: tree): node =
	match t with
	|Leaf(n) -> n
	|Tree(n,l) -> n

(*Appends child to parent's list of subtrees*)
let add_child (parent: tree) (child: tree): tree =
	match parent with
	|Leaf(n) -> Tree(n,[child])
	|Tree(n, l)-> Tree(n, List.append l [child]);;

(* Lexical/phrasal tokens combined in preorder traversal*)
let rec to_string (t: tree): string =
	match t with
	|Leaf(n) -> n
	|Tree(n, l) -> let str = n in
		let str = str^"[" in
		let f (x: string) (y: tree): string = x^(to_string y) in 
			(List.fold_left f str l)^"]";;

(*Same to_string for tree option types*)
let rec opt_to_string (t: tree option): string =
	match t with
	|None -> "None"
	|Some tr -> to_string tr;;


(*Prints a string list*)
let rec print_slist (lst: string list): unit =
	match lst with
	|[] -> ()
	|h::t -> let () = print_string (h^" ") in print_slist t;;

(*Prints a tree list*)
let rec print_tree_list(lst: tree list): unit=
	match lst with
	|[] -> ()
	|h::t -> let () = print_endline (to_string h) in 
		print_tree_list t;;


(*Prints a tree list list*)
let rec print_parses(lst: tree list list): unit =
	match lst with 
	|[] -> ()
	|h::t -> let () = print_tree_list (h) in 
		print_parses t;;

(*Extension of List.fold_left, applies f 
  following preorder traversal to all tree nodes*)
let rec fold_tree (f: 'a -> tree -> 'a)(ac: 'a)(t: tree): 'a =
	match t with
	|Leaf(s) -> f ac t
	|Tree(s, l) -> let g (ac: 'a) (t1: tree): 'a = fold_tree f ac t1 in 
		List.fold_left g (f ac t) l;;  

(*Returns length of tree*)
let rec count (t: tree): int =
	let f (i: int) (t2: tree): int = i+1 in 
		fold_tree f 0 t;;

(*Concatenates the preorder traversal of a tree into
  a string containing all the node labels*)
let rec concat(t: tree): string =
	let f (s: string)(t2: tree): string =
		let str = get_head t2 in s^str in 
			fold_tree f "" t;;


(*Determines whether n2 can be substituted for n1*)
let f_compare (n1: node) (n2: node): bool =
	if (n1 = n2) then true else
	if (n1 = "WhRel-PP") then 
		if(List.mem n2 ["whom-NP"; "which-NP"]) then true else false else
	if(n1 = "DP") then
		if(n2 = "NP-Pl") then true else false else 
	if(n1 = "Rel-Obj-DP") then 
		if(List.mem n2 ["who-NP"; "whom-NP"; "which-NP"; "whose-DP"; "that-NP"]) then true else false else
	if(n1 = "WhQ-PP") then 
		if(List.mem n2 ["which-DP"; "whose-DP"; "what-DP"; "whom-NP"; "what-DP"]) then true else false else
	if(n1 = "WhQ-NonvP-Comp") then 
		if (List.mem n2 ["who-NP"; "whose-DP"; "what-DP"; "what-NP"; "which-DP"; "whom-NP"; "What-Pl-DP"]) then true else false else
	if(n1 = "WhQ-NonvP-Adj") then 
		if(List.mem n2 ["How-AdjP"; "How-AdvP"; "Wh-PP"; "when-PP"; "where-PP"; "why-PP"]) then true else false else
	if(n1 = "Ind-S") then
		if(List.mem n2 ["S"; "Wh-Int-Dep"]) then true else false else 
	if(n1 = "TC-Adj") then 
		if (List.mem n2 ["AdjP"; "AdvP"; "PP"]) then true else false
	else false;;


(*Traverses lst and returns a copy of lst where all elements
  are unchanged except the first element for which f returns Some tree
  (that element is changed to the resultant tree from f) *)
let rec fold_option(f: tree -> tree option) (lst: tree list) (ag: tree list): tree list option=
	match lst with
	|[] -> None
	|h::t -> let out = f h in 
		match out with
		|None -> if t = [] then None
			else fold_option f t (List.append ag [h])
		|Some(tr) -> let lst = tr::t in Some(List.append ag lst);;


(*Performs TAG substitution of the child into the first appropriate leaf of the parent*)
let rec subst (parent: tree) (child: tree): tree option =
	let n2 = get_head child in 
	match parent with
	|Leaf(n1) -> if f_compare n1 n2 then Some child else None  
	|Tree(n1, l) -> let f (p: tree): tree option = subst p child in  
		let l2 = fold_option f l [] in 
		match l2 with
		|None -> None
		|Some l -> Some(Tree(n1, l));;

(*Performs TAG adjunction of the child into the first appropriate node of the parent*)
let rec adj (parent: tree) (child: tree): tree option =
	let nc = get_head child in
	if nc = "Empty" then Some parent else 
	match parent with 
	|Leaf(np) -> if f_compare np nc then Some(child) else None
	|Tree(np, lp) -> if f_compare np nc then
		(match child with
		|Leaf(_) -> None
		|Tree(_, _) -> subst child parent)
	else let f (p: tree): tree option = adj p child in 
		let l2 = fold_option f lp [] in 
		match l2 with 
		|None -> None
		|Some l -> Some(Tree(np, l));;


(*Reads only the lexical nodes of a tree,
  ignoring nonterminal symbols (phrases) *)
let rec read_tree (t: tree): string list=
	let phrases = ["VP"; "NP"; "DP"; "AdjP"; "AdvP"; "PP"; "GAP"; "TC-cxn"; "NonvP"; "VerbalP";
					"V"; "N"; "D"; "Adj"; "Adv"; "P"; "Wh-ex"; "What-DP"; "What-Pl-DP";  "What-Sing-DP";
					"How-Adj"; "How-AdvP"; "How-AdjP"; "Wh-Q"; "Wh-Adj-DP"; "Wh-Comp-DP"; "Wh-DP"; "Wh-PP";
					"FG-rel"; "Rel-Lin-DP"; "S-inf"; "whose-DP"; "which-DP"; "what-DP"; "when-PP"; "where-PP";
					"why-PP"; "Wh-PP"; "who-NP"; "what-NP"; "that-NP"; "which-NP"; "NP-Pl"; "whom-NP"; 
					"HelpV"; "WhQ-NonvP-Comp"; "WhQ-NonvP-Adj"; "Wh-Int-Dep"; "Ind-S"; "Rel-Obj-DP"; 
					"Rel-Adj-DP"; "Rel-PP-DP"; "TC-Adj"; "WhRel-PP"; "WhQ-PP"; "to-inf"] in 
	match t with 
	|Leaf(s) -> if(List.mem s phrases) then [] else [s]
	|Tree(s, l) -> let f (lst: string list) (t2: tree): string list = List.append lst (read_tree t2) in
		List.fold_left f [] l;;  

(*Removes instances of 'GAP' from a string list*)
let rec remove_gaps (lst: string list): string list=
	let f (acc: string list) (str: string): string list =
		if str = "GAP" then acc else str::acc in 
	List.fold_left f [] lst;; 

(*Determines whether parse is a sub-list of sent*)
let rec verify (parse: string list) (sent: string list): bool = 
	let rec f (lst1: string list) (lst2: string list): bool = 
		(match lst1, lst2 with
		|[], [] -> true
		|h1::t1, h2::t2 -> 
			if (h1 = h2) then f t1 t2 else false
		|[], h2::t2 -> true 
		|_,_ -> false) in 
	match sent with
	|[] -> false 
	|h::t -> if (f parse sent) then true else verify parse t;;



(*Finds all trees that represent a proper TAG combination of the input trees*)
let rec join (t1: tree)(t2: tree)(sent: string list): tree list =
	let parse1 = subst t1 t2 in
	let parse2 = subst t2 t1 in
	let parse3 = adj t1 t2 in 
	let parse4 = adj t2 t1 in 
	let parses = [parse1; parse2; parse3; parse4] in 
	let rec f (acc: tree list)(parse: tree option): tree list =
		(match parse with 
		|None -> acc
		|Some tr -> 
			if List.mem tr acc then acc
			else if verify (read_tree tr) sent then List.append acc [tr] 
			else acc) in 
	List.fold_left f [] parses;;


(*Returns a list of grammatical merges between a tree in lst1 and a tree in lst2*)
let rec permutations (lst1: tree list) (lst2: tree list)(sent: string list): tree list =
	match lst1 with
	|[] -> []
	|h1::t1 -> let rec f (acc: tree list) (tr: tree): tree list = List.append acc (join h1 tr sent) in
		List.append (List.fold_left f [] lst2) (permutations t1 lst2 sent);;
		
(*Returns a list of trees that represent a TAG combination of
  one element of each list in the input tree list list*)
let rec join_list (lst: tree list list) (sent: string list): tree list =
	match lst with 
	|[] -> []
	|h::[] -> h
	|h1::h2::[] -> permutations h1 h2 sent
	|h1::h2::h3::t -> 
		let perms = permutations h1 h2 sent in 
			if (List.length perms) > 0 then 
				let jl2 = join_list (perms::h3::t) sent in
					if(List.length jl2) > 0 then jl2
					else
						let jl3 = join_list (h2::h3::t) sent in 
						permutations h1 jl3 sent 
			else
				let jl3 = join_list (h2::h3::t) sent in 
				permutations h1 jl3 sent;;


(* All of the following elementary-tree generating functions 
   output a list of elementary trees anchored by the input string lex*)

let vp (lex: string): tree list =
	let trans = Tree("VP", [Tree("V", [Leaf(lex)]); Leaf("DP")]) in 
	let intrans = Tree("VP", [Tree("V", [Leaf(lex)])]) in
	let v = Tree("V", [Leaf(lex)]) in
	let sent_trans = Tree("S", [Leaf("DP"); trans]) in 
	let sent_intrans = Tree("S", [Leaf("DP"); intrans]) in   
		[sent_trans; sent_intrans; trans; intrans; v];;

let np (lex: string): tree list = [Tree("NP", [Tree("N", [Leaf(lex)])])];;

let np_pl (lex:string): tree list = [Tree("NP-Pl", [Tree("N-Pl", [Leaf(lex)])])];;

let dp (lex: string): tree list = 
	let phrase = Tree("DP", [Tree("D", [Leaf(lex)]); Leaf("NP")]) in 
	let det = Tree("D", [Leaf(lex)]) in [phrase; det];;

let adjp (lex: string): tree list = 
	let phrase = Tree("NP", [Tree("AdjP", [Tree("Adj", [Leaf(lex)])]); Leaf("NP")]) in 
	let pl_phrase = Tree("NP-Pl", [Tree("AdjP", [Tree("Adj", [Leaf(lex)])]); Leaf("NP-Pl")]) in 
	let adj = Tree("AdjP", [Tree("Adj", [Leaf(lex)])]) in [phrase; adj; pl_phrase];;

let advp (lex: string): tree list = 
	let left = Tree("VP", [Tree("AdvP", [Tree("Adv", [Leaf(lex)])]); Leaf("VP")]) in 
	let right = Tree("VP", [Leaf("VP"); Tree("AdvP", [Tree("Adv", [Leaf(lex)])])]) in
	let adv = Tree("AdvP", [Tree("Adv", [Leaf(lex)])]) in 
		[left; right; adv];;

let pp (lex: string): tree list = 
	let verbal = Tree("VP", [Leaf("VP"); Tree("PP", [Tree("P", [Leaf(lex)]); Leaf("DP")])]) in 
	let nominal = Tree("DP", [Leaf("DP"); Tree("PP", [Tree("P", [Leaf(lex)]); Leaf("DP")])]) in 
	let pp = Tree("PP", [Tree("P", [Leaf(lex)]); Leaf("DP")]) in
	let adj = Tree("DP", [Leaf("DP"); Tree("FG-rel", [Tree("Wh-PP", [Tree("P", [Leaf(lex)]); Leaf("WhRel-PP")]); Tree("S", 
		[Leaf("DP"); Tree("VP", [Leaf("VP"); Leaf("GAP")])])])]) in
	let adj_inf = Tree("DP", [Leaf("DP"); Tree("FG-rel", [Tree("Wh-PP", [Tree("P", [Leaf(lex)]); Leaf("WhRel-PP")]); Tree("S-inf", 
		[Leaf("to-inf"); Tree("VP", [Leaf("VP"); Leaf("GAP")])])])]) in
	let whpp = Tree("Wh-PP", [Tree("P", [Leaf(lex)]); Leaf("WhQ-PP")]) in
	 [verbal; nominal; pp; adj; whpp; adj_inf];;

let helpv (lex:string): tree list = [Tree("HelpV", [Leaf(lex)])];;

let ind_state (lex:string): tree list = 
	let adj = Tree("S", [Leaf("DP"); Tree("VP", [Tree("V", [Leaf(lex)]); Leaf("Ind-S")])]) in 
	let vp = Tree("VP", [Tree("V", [Leaf(lex)]); Leaf("Ind-S")]) in [adj; vp];;

let wh_np (lex:string): tree list = 
	[Tree(lex^"-NP", [Leaf(lex)])];;

let wh_dp (lex:string): tree list =
	[Tree(lex^"-DP", [Leaf(lex); Leaf("NP")])];;

let wh_pp (lex:string): tree list =
	[Tree(lex^"-PP", [Leaf(lex)])];;

let whp_pp (lex:string): tree list =
	[Tree("Wh-PP", [Leaf("P"); Leaf("WhP")])];; 

let what_dp (lex: string): tree list =
	let sing = Tree("What-Sing-DP", [Leaf(lex); Tree("DP", [Leaf("D"); Leaf("NP")])]) in
	let pl = Tree("What-Pl-DP", [Leaf(lex); Leaf("NP-Pl")]) in [sing; pl];;

let how_adj (lex: string): tree list = 
	let adjp = Tree("How-AdjP", [Leaf("how"); Leaf("AdjP")]) in 
	let advp = Tree("How-AdvP", [Leaf("how"); Leaf("AdvP")]) in [adjp; advp];;

(*All of the following elementary tree generating functions return elementary 
  trees anchored by the GAP null lexeme*)

let lin_s (): tree list=
	[Tree("S", [Leaf("DP"); Leaf("VP")])];;

let tc_cxn (): tree list =
	let comp = Tree("TC-cxn", [Leaf("DP"); Tree("S", [Leaf("DP"); Tree("VP", [Leaf("V"); Leaf("GAP")])])]) in
	let adj = Tree("TC-cxn", [Leaf("TC-Adj"); Tree("S", [Leaf("DP"); Tree("VP", [Leaf("VP"); Leaf("GAP")])])])
	in [comp; adj];;

let wh_ex (): tree list =
	let wh_pl = Tree("Wh-ex", [Leaf("What-Pl-DP"); Tree("S", [Leaf("DP"); Tree("VP", [Leaf("V"); Leaf("GAP")])])]) in
	let wh_sing = Tree("Wh-ex", [Leaf("What-Sing-DP"); Tree("S", [Leaf("DP"); Tree("VP", [Leaf("V"); Leaf("GAP")])])]) in 
	let adv = Tree("Wh-ex", [Leaf("How-AdvP"); Tree("S", [Leaf("DP"); Tree("VP", [Leaf("VP"); Tree("AdvP", [Leaf("GAP")])])])]) in 
	let adj = Tree("Wh-ex", [Leaf("How-AdjP"); Tree("S", [Leaf("DP"); Tree("VP", [Leaf("V"); Leaf("GAP")])])]) in
	[wh_sing; wh_pl; adv; adj];;


let wh_rel (): tree list =
	let obj = Tree("DP", [Leaf("DP"); Tree("FG-rel", [Leaf("Rel-Obj-DP"); 
		Tree("S", [Leaf("DP"); Tree("VP", [Leaf("V"); Leaf("GAP")])])])]) in 
	let adj = Tree("DP", [Leaf("DP"); Tree("FG-rel", [Leaf("Rel-Adj-DP"); Tree("S", 
		[Leaf("DP"); Tree("VP", [Leaf("VP"); Leaf("GAP")])])])]) in
	let adj_inf = Tree("DP", [Leaf("DP"); Tree("FG-rel", [Leaf("Rel-PP-DP"); Tree("S-inf", 
		[Leaf("to-inf"); Tree("VP", [Leaf("V"); Leaf("GAP")])])])]) 
	in [obj; adj; adj_inf];;


let wh_q (): tree list = 
	let comp = Tree("Wh-Q", [Leaf("WhQ-NonvP-Comp"); Tree("S-Inv-cxn", [Leaf("HelpV"); Leaf("DP");
		Tree("VP", [Leaf("V"); Leaf("GAP")])])]) in 
	let adj = Tree("Wh-Q", [Leaf("WhQ-NonvP-Adj"); Tree("S-Inv-cxn", [Leaf("HelpV"); Leaf("DP");
		Tree("VP", [Leaf("VP"); Leaf("GAP")])])]) in
	[comp; adj];;

let wh_int_dep (): tree list =
	let comp = Tree("Wh-Int-Dep", [Leaf("WhQ-NonvP-Comp"); Tree("S", 
		[Leaf("DP"); Tree("VP", [Leaf("V"); Leaf("GAP")])])]) in
	let adj = Tree("Wh-Int-Dep", [Leaf("WhQ-NonvP-Adj"); Tree("S", 
		[Leaf("DP"); Tree("VP", [Leaf("VP"); Leaf("GAP")])])]) in 
	let comp_inf = Tree("Wh-Int-Dep", [Leaf("WhQ-NonvP-Comp"); Tree("S-inf", 
		[Leaf("to-inf"); Tree("VP", [Leaf("V"); Leaf("GAP")])])]) in 
	let adj_inf = Tree("Wh-Int-Dep", [Leaf("WhQ-NonvP-Adj"); Tree("S-inf", 
		[Leaf("to-inf"); Tree("VP", [Leaf("VP"); Leaf("GAP")])])]) in 
	[comp; adj; comp_inf; adj_inf];;


(*A limited vocabulary for testing purposes*)
let lex_table = Hashtbl.create 100;;
Hashtbl.add lex_table "boy" "NP";;
Hashtbl.add lex_table "girl" "NP";;
Hashtbl.add lex_table "student" "NP";;
Hashtbl.add lex_table "mother" "NP";;
Hashtbl.add lex_table "child" "NP";;
Hashtbl.add lex_table "friend" "NP";;
Hashtbl.add lex_table "the" "DP";;
Hashtbl.add lex_table "a" "DP";;
Hashtbl.add lex_table "good" "AdjP";;
Hashtbl.add lex_table "bad" "AdjP";;
Hashtbl.add lex_table "slowly" "AdvP";;
Hashtbl.add lex_table "quickly" "AdvP";;
Hashtbl.add lex_table "smart" "AdjP";;
Hashtbl.add lex_table "saw" "VP";;
Hashtbl.add lex_table "ran" "VP";;
Hashtbl.add lex_table "ate" "VP";;
Hashtbl.add lex_table "read" "VP";;
Hashtbl.add lex_table "book" "NP";;
Hashtbl.add lex_table "books" "NP-Pl";;
Hashtbl.add lex_table "home" "NP";;
Hashtbl.add lex_table "found" "VP";;
Hashtbl.add lex_table "in" "PP";;
Hashtbl.add lex_table "to" "PP";;
Hashtbl.add lex_table "store" "NP";;
Hashtbl.add lex_table "how" "How";;
Hashtbl.add lex_table "what" "What";;
Hashtbl.add lex_table "who" "Who";;
Hashtbl.add lex_table "whom" "Who";;
Hashtbl.add lex_table "that" "That";;
Hashtbl.add lex_table "whose" "Whose";;
Hashtbl.add lex_table "which" "Which";;
Hashtbl.add lex_table "opened" "VP";;
Hashtbl.add lex_table "did" "HelpV";;
Hashtbl.add lex_table "run" "VP";;
Hashtbl.add lex_table "see" "VP";;
Hashtbl.add lex_table "when" "WhPP";;
Hashtbl.add lex_table "where" "WhPP";;
Hashtbl.add lex_table "why" "WhPP";;
Hashtbl.add lex_table "knew" "IndS";;
Hashtbl.add lex_table "know" "IndS";;
Hashtbl.add lex_table "for" "PP";;
Hashtbl.add lex_table "liked" "VP";;
Hashtbl.add lex_table "speed" "NP";;
Hashtbl.add lex_table "increased" "VP";;



(*Based on the part of speech of the input string as stored in the Hash table
  this function finds all the elementary trees anchored by str*)
let rec get_pos (str: string): tree list =
	let head = Hashtbl.find lex_table str in
	if str = "to" then let lst = List.append (pp str) (whp_pp str) in 
		List.append (lst) [Tree("to-inf", [Leaf("to")])] else 
	if head = "NP" then np str else
	if head = "VP" then vp str else
	if head = "AdjP" then adjp str else
	if head = "AdvP" then advp str else
	if head = "PP" then List.append (pp str) (whp_pp str) else
	if head = "How" then how_adj str else
	if head = "What" then List.append (List.append (what_dp str) (wh_dp str)) (wh_np str) else
	if head = "Which" then let lst = List.append (wh_dp str) (wh_np str) in 
		let whnp = wh_np str in 
		let whrel = wh_rel() in 
		List.append lst (permutations whnp whrel [str]) else 
	if head = "Whose" then 
		let whdp = wh_dp str in 
		let whrel = wh_rel() in 
		List.append whdp (permutations whdp whrel [str]) else 
	if head = "Who" then
		let whnp = wh_np str in 
		let whrel = wh_rel() in 
		List.append whnp (permutations whnp whrel [str]) else 
	if head = "That" then 
		let whnp = wh_np str in 
		let whrel = wh_rel() in 
		List.append whnp (permutations whnp whrel [str]) else
	if head = "Adj-Wh" then wh_dp str else 
	if head = "NP-Pl" then np_pl str else
	if head = "HelpV" then helpv str else
	if head = "WhPP" then wh_pp str else
	if head = "IndS" then 
		let l1 = List.append (ind_state str) (permutations (ind_state str) (wh_int_dep()) [str]) in 
		let l2 = List.append l1 (permutations (ind_state str) (lin_s()) [str]) in 
		List.append (vp str) l2 
	else dp str;;


(*Parses the input as the type of sentence specified by func: linear sentence,
  topicalized clause, wh-question etc*)
let parse_sent (func: string) (input: tree list list) (sent: string list): tree list =
	if func = "s_lin" then join_list ((lin_s())::input) sent else  
	if func = "tc_cxn" then join_list ((tc_cxn())::input) sent else
	if func = "wh_q" then join_list ((wh_q())::input) sent
	else join_list ((wh_ex())::input) sent;;


(* Returns a string list containing all the leaf labels of the input tree*)
let rec get_leaves(tr: tree): string list =
	let f (lst: string list) (t: tree): string list = 
		(match t with 
		|Leaf(n) -> List.append lst [n]
		|Tree(n, l) -> lst) in 
	fold_tree f [] tr;;


(*Returns true if the input tree contains no nonterminal symbols (i.e. phrases) in its leaf nodes
  Returns false if the tree is incomplete/contains nonterminals in its leaves*)
let rec is_complete (tr:tree): bool =
	let phrases = ["VP"; "NP"; "DP"; "AdjP"; "AdvP"; "PP"; "TC-cxn"; "NonvP"; "VerbalP";
					"V"; "N"; "D"; "Adj"; "Adv"; "P"; "Wh-ex"; "What-DP"; "What-Pl-DP";  "What-Sing-DP";
					"How-Adj"; "How-AdvP"; "How-AdjP"; "Wh-Q"; "Wh-Adj-DP"; "Wh-Comp-DP"; "Wh-DP"; "Wh-PP";
					"FG-rel"; "Rel-Lin-DP"; "S-inf"; "whose-DP"; "which-DP"; "what-DP"; "when-PP"; "where-PP";
					"why-PP"; "Wh-PP"; "who-NP"; "what-NP"; "that-NP"; "which-NP"; "NP-Pl"; "whom-NP"; 
					"HelpV"; "WhQ-NonvP-Comp"; "WhQ-NonvP-Adj"; "Wh-Int-Dep"; "Ind-S"; "Rel-Obj-DP"; 
					"Rel-Adj-DP"; "Rel-PP-DP"; "TC-Adj"; "WhRel-PP"; "WhQ-PP"; "to-inf"]  in 
	let leaves = get_leaves tr in 
	let rec helper (lst: string list): bool =
		match lst with 
		|[] -> true 
		|h::t -> if (List.mem h phrases) then false else helper t in 
	helper leaves;;

(*Removes parses which contain nonterminal elements in leaf nodes*)
let rec remove_incompletes (parses: tree list): tree list =
	let f (lst: tree list) (tr: tree): tree list =
		if is_complete tr then tr::lst else lst in 
	List.fold_left f [] parses;;


(*Gets the input sentences and parses them using the TAG-CxG algorithm*)
let rec run (str: string): unit = 
	let sent = String.split_on_char ' ' str in 
	let f (acc: tree list list) (word: string): tree list list =
		List.append acc [(get_pos word)] in 
	let input = List.fold_left f [] sent in 
	let parses = parse_sent "s_lin" input sent in 
	let completes = remove_incompletes parses in 
		if (List.length completes) > 0
			then print_tree_list completes else 
	let parses = parse_sent "tc_cxn" input sent in  
	let completes = remove_incompletes parses in 
		if (List.length completes) > 0
			then print_tree_list completes else
	let parses = parse_sent "wh_q" input sent in 
	let completes = remove_incompletes parses in  
		if (List.length completes) > 0
			then print_tree_list completes else
	let parses = parse_sent "wh_ex" input sent in 
	let completes = remove_incompletes parses in 
		if (List.length completes) > 0
			then print_tree_list completes 
	else 
		let () = print_endline "No complete parses: " in ();;


(*Parses a series of correct and incorrect filler-gap sentences*)
let main (): unit =
	let () = run("the good child the student liked") in
	let () = run("the good child the mother knew the student liked") in 
	let () = run("quickly the student ran") in
	let () = run("quickly the student who the child saw ran") in  
	let () = run("in the store the child ran quickly") in 
	let () = run("what a good book the student read") in
	let () = run("what good books the student read quickly") in 
	let () = run("how quickly the mother knew the child read") in 
	let () = run("how quickly the child read the book") in 
	let () = run("what book did the good child read quickly") in
	let () = run("what book did the mother know the good child read quickly") in 
	let () = run("what did the child see") in 
	let () = run("whom did the child whom the student knew see") in 
	let () = run("why did the child run to the store quickly") in 
	let () = run("when did the good child run to the store") in 
	let () = run("where did the child whom the student knew run") in 
	let () = run("what books did the child read") in 
	let () = run("whose mother did the student see in the store") in 
	let () = run("who did the child see in the store") in 
	let () = run("what book did the child whose mother the student knew read") in 
	let () = run("in which store did the child run") in 
	let () = run("how quickly did the child run") in 
	let () = run("the student knew how quickly the child ran") in 
	let () = run("the student knew the child knew how quickly the boy ran") in 
	let () = run("the girl knew what the good child saw in the store") in 
	let () = run("the boy knew why the child ran to the store quickly") in 
	let () = run("the boy whom the girl saw knew what book the student read") in 
	let () = run("the boy whose mother the girl saw knew when the child ran to the store") in
	let () = run ("the good boy knew where the girl ran") in 
	let () = run ("the boy knew where to run") in 
	let () = run ("the boy knew who to see in the store") in
	let () = run ("the boy knew whose child the girl saw in the store") in 
	let () = run ("the girl knew how quickly to run to the store") in 
	let () = run ("the girl knew in which store to see the child") in 
	let () = run ("the girl knew what books to read") in 
	let () = run ("the student knew whose mother to see") in
	let () = run ("the boy who the child knew ran") in
	let () = run ("the boy saw the book which the child read quickly") in 
	let () = run ("the girl whose mother the boy knew read a book") in 
	let () = run ("the store in which a child ran opened") in 
	let () = run ("the girl whom the boy knew read a book quickly") in 
	let () = run ("the boy read the book that the girl read in the store") in 
	let () = run ("the store in which to run opened") in 
	let () = run ("the girl that the boy knew saw the student") in 
	let () = run ("where did the girl know who ran") in 
	let () = run ("who did the girl know when the boy saw") in 
	let () = run ("the store what the child saw opened") in 
	let () = run ("the speed how quickly the girl ran increased") in 
	let () = run ("the book did the girl read") in 
	let () = run ("the boy whose the girl saw mother read a book") in 
	run("the child whom the mother saw ran");;

main();; 






