open Proj2_types;;

let getStartSymbol (g : grammar) : string =
	let (startSymbol, _) = g in
	startSymbol
;;


let rec nonTerminalFromGrammar (nonTerminals : string list) (sets : (string * string list) list) =
	match sets with
	| [] -> nonTerminals
	| h::t ->
		(* get nonTerminal from nonTerminal * symbols tuple *)
		let (nonTerminal, _) = h in
		(* prepend nonTerminal *)
		let nonTerminals = nonTerminal::nonTerminals in
		(* recurse on tail *)
		nonTerminalFromGrammar nonTerminals t
;;

let getNonterminals (g : grammar) : string list =
	let (_, sets) = g in
	nonTerminalFromGrammar [] sets
;;


(* takes a symbolMap and maps each string from a string list to an empty set *)
let rec buildEmptySets (sets : symbolMap) (nonTerminals : string list) : symbolMap =
	match nonTerminals with
	| [] -> sets
	| h::t ->
		(* insert first nonTerminal into Map with value [] *)
		let sets = SMap.add h SymbolSet.empty sets in
		(* recurse with tail *)
		buildEmptySets sets t
;;

(* https://ocaml.org/learn/tutorials/map.html *)
(* https://ocaml.org/learn/tutorials/set.html *)
let getInitFirstSets (g : grammar) : symbolMap =
	let nonTerminals = getNonterminals g in
	(* get empty sets for each nonTerminal *)
	buildEmptySets SMap.empty nonTerminals
;;


let getInitFollowSets (g : grammar) : symbolMap =
	let nonTerminals = getNonterminals g in
	(* get empty sets for each nonTerminal *)
	let sets = buildEmptySets SMap.empty nonTerminals in
	(* create the set for the start symbol *)
	let startSymbol = getStartSymbol g in
	let startSymbolSet = SymbolSet.add "eof" SymbolSet.empty in
	(* insert ["eof"] into sets at start symbol *)
	SMap.add startSymbol startSymbolSet sets
;;


(* not having an accumulator hurts me *)
(* uses firstMaps to return possible firsts for the sequence *)
let rec computeFirstSet (first : symbolMap) (symbolSeq : string list) : SymbolSet.t =
	match symbolSeq with
	| [] -> SymbolSet.add "eps" SymbolSet.empty
	| firstInSeq::nextInSeq ->
		(* if firstInSeq is nonTerminal *)
		if SMap.mem firstInSeq first then
			(* add each symbol from firstInSeq's first set *)
			let rec takeFirstSet = fun symbols -> fun firstSet ->
				match symbols with
				| [] ->
					(* stop if empty *)
					firstSet
				| "eps"::nextSymbols ->
					(* also get first of next in seq if first in seq could be eps *)
					let nextFirstSet = computeFirstSet first nextInSeq in
					(* merge sets *)
					let firstSet = SymbolSet.union nextFirstSet firstSet in
					(* continue *)
					takeFirstSet nextSymbols firstSet
				| symbol::nextSymbols ->
					(* add to set if existing *)
					let firstSet = SymbolSet.add symbol firstSet in
					(* continue *)
					takeFirstSet nextSymbols firstSet
			in (* end takeFirstSet *)
			(* get the first symbols for the firstInSeq *)
			let symbols = SMap.find firstInSeq first in
			let symbols = SymbolSet.elements symbols in
			(* for each symbol, insert to set *)
			takeFirstSet symbols SymbolSet.empty
		(* if firstInSeq is terminal *)
		else
			(* add the symbol *)
			SymbolSet.add firstInSeq SymbolSet.empty
;;

(* recurses through grammer to get firstSets for each symbol using the firstMap *)
let recurseFirstSets (g : grammar) (first : symbolMap) firstFunc : symbolMap =
	(* recurse through the list of sequences and applys firstFun to the sequences *)
	let rec helper = fun (pairs : (string * string list) list) -> fun first ->
		match pairs with
		(* end on clear *)
		| [] -> first
		(* insert to first set, the first set for first sequence *)
		| firstInPairs::nextInPairs ->
			let (symbol, sequence) = firstInPairs in
			(* get firstSet for select sequence *)
			let set = firstFunc first sequence in
			let firstSet = SMap.find symbol first in
			let firstSet = SymbolSet.union set firstSet in
			(* update firstMap *)
			let first = SMap.add symbol firstSet first in
			(* continue *)
			helper nextInPairs first
	in (* end helper *)
	let (_, pairs) = g in
	helper pairs first
;;

(* repeat recurseFirstSets until no more changes *)
let rec getFirstSets (g : grammar) (first : symbolMap) firstFunc : symbolMap =
	(* get first sets *)
	let newFirstMap = recurseFirstSets g first firstFunc in
	let areSetsEqual = fun set1 -> fun set2 ->
		if SymbolSet.equal set1 set2 then
			true
		else
			false
	in (* end areSetsEqual *)
	if SMap.equal areSetsEqual newFirstMap first then
		(* if equal, return *)
		newFirstMap
	else
		(* if not equal, recurseFirstSets again *)
		getFirstSets g newFirstMap firstFunc
;;


(* a rule is inputted as its nonTerminal, nt, and sequence, symbolSeq *)
(* update follow set using the given rule *)
let rec updateFollowSet (first : symbolMap) (follow : symbolMap) (nt : string) (symbolSeq : string list) : symbolMap =
	(* recurse through the seq *)
	match symbolSeq with
	| [] ->
		(* end on clear *)
		follow
	| firstInSeq::nextInSeq ->
		(* if firstInSeq is a nonTerminal, update follow set *)
		if SMap.mem firstInSeq first then
			match nextInSeq with
			| [] ->
				(* if firstInSeq is lastInSeq *)
				let insertSet = SMap.find nt follow in
				let followSet = SMap.find firstInSeq follow in
				(* union with follow set of nonTerminal that owns sequence *)
				let followSet = SymbolSet.union insertSet followSet in
				(* update followMap *)
				let follow = SMap.add firstInSeq followSet follow in
				(* end on clear *)
				follow
			| firstNextInSeq::_ ->
				(* if firstInSeq has a next *)
				(* if next is a nonTerminal *)
				if SMap.mem firstNextInSeq first then
					let rec firstUnion = fun insertList -> fun followSet ->
						match insertList with
						| [] ->
							(* end on clear *)
							followSet
						| "eps"::nextInInsert ->
							let insertList = SMap.find firstNextInSeq follow in
							(* if first set of next has an epsilon, also union follow set *)
							let followSet = SymbolSet.union insertList followSet in
							(* continue *)
							firstUnion nextInInsert followSet
						| firstInInsert::nextInInsert ->
							(* insert symbol *)
							let followSet = SymbolSet.add firstInInsert followSet in
							(* continue *)
							firstUnion nextInInsert followSet
					in (* end firstUnion *)
					let insertList = SMap.find firstNextInSeq first in
					let insertList = SymbolSet.elements insertList in
					let followSet = SMap.find firstInSeq follow in
					(* union with first set of next *)
					let followSet = firstUnion insertList followSet in
					(* update followMap *)
					let follow = SMap.add firstInSeq followSet follow in
					(* continue *)
					updateFollowSet first follow nt nextInSeq
				(* if next is a terminal *)
				else
					let followSet = SMap.find firstInSeq follow in
					(* add next to follow set *)
					let followSet = SymbolSet.add firstNextInSeq followSet in
					(* update followMap *)
					let follow = SMap.add firstInSeq followSet follow in
					(* continue *)
					updateFollowSet first follow nt nextInSeq
		(* if firstInSeq is a terminal, continue *)
		else
			updateFollowSet first follow nt nextInSeq
;;

(* update follow sets for each rule *)
let recurseFollowSets (g : grammar) (first : symbolMap) (follow : symbolMap) followFunc : symbolMap =
	(* for each rule, update followMap *)
	let rec checkRules = fun (rulesList : (string * string list) list) -> fun follow ->
		match rulesList with
		| [] ->
			(* end on clear *)
			follow
		| (nonTerminal, sequence)::nextRules ->
			(* update follow *)
			let follow = followFunc first follow nonTerminal sequence in
			(* continue *)
			checkRules nextRules follow
	in (* end checkNonTerminal *)
	let (_, rulesList) = g in
	checkRules rulesList follow
;;

(* repeat recurseFirstSets until no more changes *)
let rec getFollowSets (g : grammar) (first : symbolMap) (follow : symbolMap) followFunc : symbolMap =
	(* get new follow map *)
	let newFollowMap = recurseFollowSets g first follow followFunc in
	let areSetsEqual = fun set1 -> fun set2 ->
		if SymbolSet.equal set1 set2 then
			true
		else
			false
	in (* end areSetsEqual *)
	if SMap.equal areSetsEqual newFollowMap follow then
		(* if equal, return *)
		newFollowMap
	else
		(* if not equal, recurseFirstSets again *)
		getFollowSets g first newFollowMap followFunc
;;

(* list of tuples, rule and set of predict symbols *)
(* trap? should this be recursive? *)
let rec getPredictSets (g : grammar) (first : symbolMap) (follow : symbolMap) firstFunc : ((string * string list) * SymbolSet.t) list =
	let rec helper = fun (rulesList : (string * string list) list) -> fun predictSetList ->
		match rulesList with
		| [] ->
			(* end on clear *)
			predictSetList
		| (nonTerminal, sequence)::nextRules ->
			(* get first set of sequence *)
			let firstSet = firstFunc first sequence in
			(* if contains eps *)
			if SymbolSet.mem "eps" firstSet then
				(* remove eps *)
				let firstSet = SymbolSet.remove "eps" firstSet in
				(* also include follow set of nonTerminal *)
				let followSet = SMap.find nonTerminal follow in
				(* union first set of seq and follow set of nonTerminal *)
				let predictSet = SymbolSet.union firstSet followSet in
				(* update predictSetList *)
				let predictSetList = ((nonTerminal, sequence), predictSet)::predictSetList in
				(* continue *)
				helper nextRules predictSetList
			(* if does not contain eps *)
			else
				(* set first set of seq as the predict set *)
				let predictSetList = ((nonTerminal, sequence), firstSet)::predictSetList in
				(* continue *)
				helper nextRules predictSetList
	in (* end helper *)
	let (_, rulesList) = g in
	helper rulesList []
;;

let tryDerive (g : grammar) (inputStr : string list) : bool =
(*	let print_stringList = fun l ->
		let _ = List.iter (Printf.printf "\t%s") l in
		Printf.printf "\n"
	in
*)
	(* get initial blank maps *)
	let firstMap = getInitFirstSets g in
	let followMap = getInitFollowSets g in
	(* fill maps *)
	let firstMap = getFirstSets g firstMap computeFirstSet in
	let followMap = getFollowSets g firstMap followMap updateFollowSet in
	let predictSetsList = getPredictSets g firstMap followMap computeFirstSet in
	(* setup stack of nonTerminals*)
	let (startSymbol, _) = g in
	let stack = [startSymbol] in
	
	(* check the current top of stack with current symbol in sequence to get possible rule *)
	(* returns predict set list with unrelated rules removed up to first related rule at top *)
	(* if no rule found, return empty list *)
	let rec filterRules = fun nonTerminal -> fun symbol -> fun (predictSetsList : ((string * string list) * SymbolSet.t) list) ->
		match predictSetsList with
		| [] ->
			(* invalid, no sequence found for symbol under nonTerminal *)
			[]
		| ((ruleNonTerminal, ruleSeq), set)::nextPredictSets ->
			(* check if rule applies to current nonTerminal of stack *)
			if (ruleNonTerminal = nonTerminal) && (SymbolSet.mem symbol set) then
				(* return predict sets list *)
				predictSetsList
			(* if rule does not match nonTerminal nor symbol is in predictSet, continue to next predictSet *)
			else
				(* continue *)
				filterRules nonTerminal symbol nextPredictSets
	in (* end filterRules *)
	let rec matchTerminals = fun str -> fun seq ->
		match seq with
		| [] ->
			(* end when possible sequence is cleared *)
			(str, seq, true)
		| firstInSeq::nextInSeq ->
			(* if firstInSeq is a nonTerminal, stop *)
			if SMap.mem firstInSeq firstMap then
				(str, seq, true)
			(* if firstInSeq is a terminal *)
			else
				(* check if str matches the terminal *)
				match str with
				| [] ->
					(* if string is empty, string doesn't match *)
					([], [], false)
				| firstInString::restOfString ->
					(* if matches *)
					if firstInString = firstInSeq then
						(* remove from string and seq and continue removing terminals *)
						matchTerminals restOfString nextInSeq
					(* if string doesn't match *)
					else
						([], [], false)
	in (* end matchTerminals *)
	let rec matchNonTerminals = fun stack -> fun str -> fun tryPredictSetsList ->
(*		let _ = Printf.printf "Matching nonTerminals with:\n" in
		let _ = print_stringList stack in
		let _ = print_stringList str in
*)		match stack with
		| [] ->
			(* end on stack empty *)
			(* str may or may not be empty *)
			(stack, str)
		| firstInStack::nextInStack ->
			(* if stack exists *)
			(* if firstInStack is a nonTerminal *)
			if SMap.mem firstInStack firstMap then
				let (firstInStr, nextInStr) =
					match str with
					| [] ->
						(* string doesn't exist, so we will use eof in predict sets *)
						("eof", [])
					| firstInStr::nextInStr ->
						(* string exists, so predict using first in string *)
						(firstInStr, nextInStr)
				in (* end (firstInStr, nextInStr) *)
				(* remove from predict set sets that we cannot expand to *)
				let tryPredictSetsList = filterRules firstInStack firstInStr tryPredictSetsList in
				match tryPredictSetsList with
				| [] ->
					(* if we can't expand to anything *)
					(stack, str)
				| ((_, seq), _)::nextPredictSets ->
					(* if we can expand *)
					(* match terminals of str and sequence *)
					let (newStr, sequence, isMatched) = matchTerminals str seq in
					if isMatched then
						(* try to continue matching *)
						let newStack = List.append sequence nextInStack in
(*						let _ = Printf.printf "\tExpanded %s to:\n\t" firstInStack in
						let _ = print_stringList seq in
*)						let (newStack, newStr) = matchNonTerminals newStack newStr predictSetsList in
						(* matched *)
						if (newStack = []) && (newStr = []) then
							match newStack with
							| [] ->
								(* if finished *)
								(newStack, newStr)
							| _::_ ->
								(* if this sequence has more terminals after first nonTerminals *)
								(* continue matching *)
								matchNonTerminals newStack newStr predictSetsList
						(* if failed to match *)
						else
(*							let _ = Printf.printf "Revert:\n" in
*)							(* get next possible sequence *)
							matchNonTerminals stack str nextPredictSets
					(* cannot match terminals *)
					else
						(stack, str)
			(* if firstInStack is a terminal *)
			else
				(* remove terminals from stack and str *)
				let (newStr, newStack, isMatched) = matchTerminals str stack in
				if isMatched then
					(* continue matchingNonTerminals *)
					matchNonTerminals newStack newStr predictSetsList
				(* if cannot remove terminals *)
				else
					(stack, str)
	in (* end matchNonTerminals *)
	let (finalStack, finalString) = matchNonTerminals stack inputStr predictSetsList in
	if (finalStack = []) && (finalString = []) then
		true
	else
		false
;;


let tryDeriveTree (g : grammar) (inputStr : string list) : parseTree =
	(* YOUR CODE GOES HERE *)
Terminal "empty";;


let genParser g = tryDerive g;;
let genTreeParser g = tryDeriveTree g;;
