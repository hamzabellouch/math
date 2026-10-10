import Mathlib
import OAI.Computability.MinUncut.Machines.RuntimeModel2

namespace OAI

namespace MinUncutGames.Foundations.PCP.AlphabetTable.Addresses

open MinUncutGames.Foundations.Hastad
open Enumeration

abbrev Terms := List (Fin 5 × Nat)

structure Field (bound : Nat) where
  terms : Terms
  offset : Fin bound

def values (n m edge tail head : Nat) : Fin 5 → Nat := ![n, m, edge, tail, head]

def eval {bound : Nat} (field : Field bound) (inputs : Fin 5 → Nat) : Nat :=
  Emitter.affineValue field.terms inputs field.offset.val

def fieldBound (q : Nat) : Nat :=
  12 * localCount q + tapeCount q + pairTapeCount q + 1

theorem fieldBound_pos (q : Nat) : 0 < fieldBound q := by
  unfold fieldBound
  omega

theorem tapeCount_lt_bound (q : Nat) : tapeCount q < fieldBound q := by
  unfold fieldBound
  omega

theorem pairTapeCount_lt_bound (q : Nat) : pairTapeCount q < fieldBound q := by
  unfold fieldBound
  omega

theorem localCount_lt_bound (q : Nat) : localCount q < fieldBound q := by
  unfold fieldBound
  omega

theorem local_add_pair_lt_bound (q : Nat) : localCount q + pairTapeCount q < fieldBound q := by
  unfold fieldBound
  omega

theorem twelve_local_lt_bound (q : Nat) : 12 * localCount q < fieldBound q := by
  unfold fieldBound
  omega

def zeroOffset (q : Nat) : Fin (fieldBound q) := ⟨0, fieldBound_pos q⟩

def eventOffset (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q)) : Fin (fieldBound q) :=
  ⟨(localEventEquiv q event).val,
    (localEventEquiv q event).isLt.trans (localCount_lt_bound q)⟩

def rawQueryOffset (q : Nat) : Queries.RawQuery q → Fin (fieldBound q)
  | .inl (_, tape) =>
    ⟨(cubeEquiv q tape).val, (cubeEquiv q tape).isLt.trans (tapeCount_lt_bound q)⟩
  | .inr tape =>
    ⟨(pairCubeEquiv q tape).val, (pairCubeEquiv q tape).isLt.trans (pairTapeCount_lt_bound q)⟩

def reverseOffset (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : Fin (fieldBound q) :=
  ⟨(localEventEquiv q event).val * 12 + slot.val * 2 + bitValue (!orientation), by
    have he := (localEventEquiv q event).isLt
    have hs := slot.isLt
    have hb : bitValue (!orientation) < 2 := by
      simpa only [boolEquiv_val] using (boolEquiv (!orientation)).isLt
    have hbound := twelve_local_lt_bound q
    omega⟩

def headerVertices (q : Nat) : Field (fieldBound q) :=
  ⟨[(0, tapeCount q), (1, localCount q + pairTapeCount q)], zeroOffset q⟩

def headerDarts (q : Nat) : Field (fieldBound q) :=
  ⟨[(1, 12 * localCount q)], zeroOffset q⟩

def eventVertexField (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q)) :
    Field (fieldBound q) :=
  ⟨[(2, localCount q)], eventOffset q event⟩

def vertexQueryTerms (q : Nat) (side : Bool) : Terms :=
  [(1, localCount q), (if side then 4 else 3, tapeCount q)]

def edgeQueryTerms (q : Nat) : Terms :=
  [(1, localCount q), (0, tapeCount q), (2, pairTapeCount q)]

def rawQueryTerms (q : Nat) : Queries.RawQuery q → Terms
  | .inl (side, _) => vertexQueryTerms q side
  | .inr _ => edgeQueryTerms q

def rawQueryField (q : Nat) (query : Queries.RawQuery q) : Field (fieldBound q) :=
  ⟨rawQueryTerms q query, rawQueryOffset q query⟩

def reverseDartField (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : Field (fieldBound q) :=
  ⟨[(2, 12 * localCount q)], reverseOffset q event slot orientation⟩

theorem headerVertices_eval (q n m edge tail head : Nat) :
    eval (headerVertices q) (values n m edge tail head) = vertexCount n m q := by
  simp [eval, headerVertices, values, zeroOffset, Emitter.affineValue,
    vertexCount, eventCount, addressCount, Nat.mul_add,
    Nat.mul_comm, Nat.add_comm, Nat.add_assoc]

theorem headerDarts_eval (q n m edge tail head : Nat) :
    eval (headerDarts q) (values n m edge tail head) = dartCount m q := by
  simp [eval, headerDarts, values, zeroOffset, Emitter.affineValue,
    dartCount, eventCount, Nat.mul_comm, Nat.mul_assoc]

theorem eventVertexField_eval (n m q : Nat) (edge : Fin m)
    (event : AlphabetGraph.LocalEvent (Fin q)) (tail head : Nat) :
    eval (eventVertexField q event) (values n m edge.val tail head) =
      (vertexEquiv n m q (.inl (edge, event))).val := by
  rw [vertexEquiv_event_val, eventEquiv_val]
  simp [eval, eventVertexField, eventOffset, values, Emitter.affineValue, Nat.mul_comm]

theorem rawQueryField_eval (n m q : Nat) (edge : Fin m) (tail head : Fin n)
    (query : Queries.RawQuery q) :
    eval (rawQueryField q query) (values n m edge.val tail.val head.val) =
      (vertexEquiv n m q (.inr (Queries.globalize tail head edge query))).val := by
  cases query with
  | inl query =>
    rcases query with ⟨side, tape⟩
    cases side <;>
      simp [eval, rawQueryField, rawQueryTerms, vertexQueryTerms, rawQueryOffset,
        values, Emitter.affineValue, Queries.globalize, eventCount,
        Nat.mul_comm, Nat.add_assoc]
  | inr tape =>
    simp [eval, rawQueryField, rawQueryTerms, edgeQueryTerms, rawQueryOffset,
      values, Emitter.affineValue, Queries.globalize, eventCount,
      Nat.mul_comm, Nat.add_assoc]

theorem reverseDartField_eval (n m q : Nat) (edge : Fin m)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (tail head : Nat) :
    eval (reverseDartField q event slot orientation) (values n m edge.val tail head) =
      (dartEquiv m q (QueryIncidence.reverse (((edge, event), slot), orientation))).val := by
  rw [dartEquiv_reverse_val, eventEquiv_val]
  simp [eval, reverseDartField, reverseOffset, values, Emitter.affineValue,
    Nat.mul_add, Nat.mul_comm, Nat.mul_assoc,
    Nat.add_assoc]

def queryEventTerms (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) : Terms :=
  rawQueryTerms q (Queries.query (fun _ _ => false) event slot)

theorem rawQueryTerms_query (q : Nat) (P : Fin q → Fin q → Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) :
    rawQueryTerms q (Queries.query P event slot) = queryEventTerms q event slot := by
  rcases event with ⟨kind, ⟨side, tape⟩, f, g, r₀, r₁, r₂⟩
  by_cases hk₀ : kind = 0 <;> by_cases hk₁ : kind = 1 <;> by_cases hk₂ : kind = 2 <;>
    simp only [queryEventTerms, Queries.query, hk₀, hk₁, hk₂, ite_true, ite_false]
  all_goals split_ifs <;> rfl

def queryEventOffset (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (P : Fin q → Fin q → Bool) : Fin (fieldBound q) :=
  rawQueryOffset q (Queries.query P event slot)

def fieldForQueryEvent (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (P : Fin q → Fin q → Bool) : Field (fieldBound q) :=
  ⟨queryEventTerms q event slot, queryEventOffset q event slot P⟩

theorem fieldForQueryEvent_eq_rawQueryField (q : Nat)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6)
    (P : Fin q → Fin q → Bool) :
    fieldForQueryEvent q event slot P = rawQueryField q (Queries.query P event slot) := by
  unfold fieldForQueryEvent queryEventOffset rawQueryField
  rw [rawQueryTerms_query]

theorem fieldForQueryEvent_eval (n m q : Nat) (edge : Fin m) (tail head : Fin n)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6)
    (P : Fin q → Fin q → Bool) :
    eval (fieldForQueryEvent q event slot P) (values n m edge.val tail.val head.val) =
      (vertexEquiv n m q
        (.inr (Queries.globalize tail head edge (Queries.query P event slot)))).val := by
  rw [fieldForQueryEvent_eq_rawQueryField]
  exact rawQueryField_eval n m q edge tail head _

theorem fieldForQueryEvent_eval_verifier (n m q : Nat)
    (G : ConstraintGraph (Fin n) (Fin m) (Fin q)) (edge : Fin m)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) :
    eval (fieldForQueryEvent q event slot (G.accepts edge))
      (values n m edge.val (G.tail edge).val (G.head edge).val) =
      (vertexEquiv n m q (.inr ((AlphabetGraph.verifier G).query (edge, event) slot))).val := by
  rw [← Queries.globalize_query G edge event slot]
  exact fieldForQueryEvent_eval n m q edge (G.tail edge) (G.head edge) event slot _

def dartTailTerms (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : Terms :=
  if orientation then queryEventTerms q event slot else [(2, localCount q)]

def dartTailOffset (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) (P : Fin q → Fin q → Bool) : Fin (fieldBound q) :=
  if orientation then queryEventOffset q event slot P else eventOffset q event

def fieldForDartTail (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) (P : Fin q → Fin q → Bool) : Field (fieldBound q) :=
  ⟨dartTailTerms q event slot orientation, dartTailOffset q event slot orientation P⟩

theorem fieldForDartTail_eval (n m q : Nat) (edge : Fin m) (tail head : Fin n)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (P : Fin q → Fin q → Bool) :
    eval (fieldForDartTail q event slot orientation P)
      (values n m edge.val tail.val head.val) =
      (vertexEquiv n m q (if orientation then
        .inr (Queries.globalize tail head edge (Queries.query P event slot))
        else .inl (edge, event))).val := by
  cases orientation with
  | false => exact eventVertexField_eval n m q edge event tail.val head.val
  | true => exact fieldForQueryEvent_eval n m q edge tail head event slot P

def CoefficientsBounded (q : Nat) (terms : Terms) : Prop :=
  ∀ term ∈ terms, term.2 < fieldBound q

theorem headerVertices_coefficients (q : Nat) : CoefficientsBounded q (headerVertices q).terms := by
  simp only [CoefficientsBounded, headerVertices, List.mem_cons, List.not_mem_nil, or_false]
  intro term h
  rcases h with rfl | rfl
  · exact tapeCount_lt_bound q
  · exact local_add_pair_lt_bound q

theorem headerDarts_coefficients (q : Nat) : CoefficientsBounded q (headerDarts q).terms := by
  intro term h
  have heq : term = (1, 12 * localCount q) := by simpa [headerDarts] using h
  subst term
  exact twelve_local_lt_bound q

theorem eventVertexField_coefficients (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q)) :
    CoefficientsBounded q (eventVertexField q event).terms := by
  intro term h
  have heq : term = (2, localCount q) := by simpa [eventVertexField] using h
  subst term
  exact localCount_lt_bound q

theorem rawQueryTerms_coefficients (q : Nat) (query : Queries.RawQuery q) :
    CoefficientsBounded q (rawQueryTerms q query) := by
  cases query with
  | inl query =>
    rcases query with ⟨side, tape⟩
    intro term h
    simp only [rawQueryTerms, vertexQueryTerms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact localCount_lt_bound q
    · exact tapeCount_lt_bound q
  | inr tape =>
    intro term h
    simp only [rawQueryTerms, edgeQueryTerms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact localCount_lt_bound q
    · exact tapeCount_lt_bound q
    · exact pairTapeCount_lt_bound q

theorem queryEventTerms_coefficients (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) : CoefficientsBounded q (queryEventTerms q event slot) :=
  rawQueryTerms_coefficients q _

theorem reverseDartField_coefficients (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) :
    CoefficientsBounded q (reverseDartField q event slot orientation).terms := by
  intro term h
  have heq : term = (2, 12 * localCount q) := by simpa [reverseDartField] using h
  subst term
  exact twelve_local_lt_bound q

theorem rawQueryTerms_length_le (q : Nat) (query : Queries.RawQuery q) :
    (rawQueryTerms q query).length ≤ 3 := by
  cases query with
  | inl query => rcases query with ⟨side, tape⟩; simp [rawQueryTerms, vertexQueryTerms]
  | inr tape => simp [rawQueryTerms, edgeQueryTerms]

theorem queryEventTerms_length_le (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) : (queryEventTerms q event slot).length ≤ 3 :=
  rawQueryTerms_length_le q _

theorem dartTailTerms_coefficients (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) :
    CoefficientsBounded q (dartTailTerms q event slot orientation) := by
  cases orientation with
  | false => exact eventVertexField_coefficients q event
  | true => exact queryEventTerms_coefficients q event slot

theorem dartTailTerms_length_le (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) :
    (dartTailTerms q event slot orientation).length ≤ 3 := by
  cases orientation with
  | false => simp [dartTailTerms]
  | true => exact queryEventTerms_length_le q event slot

theorem offset_lt {bound : Nat} (field : Field bound) : field.offset.val < bound :=
  field.offset.isLt

end MinUncutGames.Foundations.PCP.AlphabetTable.Addresses

namespace MinUncutGames.Foundations.PCP.AlphabetTable.EmitRows

open Turing
open MinUncutGames.Foundations.Complexity
open Emitter

abbrev Context (q : Nat) := Vector Bool (q * q) × Bool
abbrev RowCommand (q : Nat) := Command 5 (Context q) (Addresses.fieldBound q)

def relationBits (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : List (Context q → Bool) :=
  List.ofFn fun index : Fin 4096 => fun context =>
    (Relations.relationFromTable context.1 context.2 event slot orientation)[index]

private theorem vector_list_ofFn {α : Type} {n : Nat} (vector : Vector α n) :
    List.ofFn (fun index : Fin n => vector[index]) = vector.toList := by
  have equality := congrArg Vector.toList (Vector.ofFn_getElem (xs := vector))
  simpa only [Vector.toList_ofFn, Fin.getElem_fin] using equality

private theorem bitValues_ofFn {σ : Type} {n : Nat}
    (relation : σ → Vector Bool n) (context : σ) :
    (List.ofFn (fun index : Fin n => fun state => (relation state)[index])).map
      (fun bit => if bit context then 1 else 0) =
      (relation context).toList.map GraphTables.bitWord := by
  rw [← vector_list_ofFn (relation context)]
  simp only [List.map_ofFn]
  rfl

theorem relationBits_values (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) (context : Context q) :
    (relationBits q event slot orientation).map (fun bit => if bit context then 1 else 0) =
      GraphTables.relationWords
        (Relations.relationFromTable context.1 context.2 event slot orientation) := by
  exact bitValues_ofFn (fun state : Context q =>
    Relations.relationFromTable state.1 state.2 event slot orientation) context

def rowCommands (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : List (RowCommand q) :=
  affineCommands (Addresses.dartTailTerms q event slot orientation)
      (fun context => Addresses.dartTailOffset q event slot orientation
        (Relations.oldPredicate context.1)) ++
    affineCommands (Addresses.reverseDartField q event slot orientation).terms
      (fun _ => (Addresses.reverseDartField q event slot orientation).offset) ++
    bitCommands (relationBits q event slot orientation)

def rowContext {q : Nat} (input : GenericGraphTables.Table q) (edge : Fin input.darts) : Context q :=
  let old := input.rows[edge]
  (old.relation, decide (old.tail = input.rows[old.reverseIndex].tail))

def rowValues {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) : Fin 5 → Nat :=
  let old := input.rows[edge]
  Addresses.values input.vertices input.darts edge.val old.tail.val
    input.rows[old.reverseIndex].tail.val

private theorem encodedRow {n m : Nat} (row : GraphTables.DartRow n m) :
    encodeWords (GraphTables.rowWords row) =
      encodeWord row.tail.val ++ (encodeWord row.reverseIndex.val ++
        encodeWords (GraphTables.relationWords row.relation)) := by
  simp only [GraphTables.rowWords, List.cons_append, List.nil_append, encodeWords]

theorem rowCommands_bits {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) :
    (rowCommands q event slot orientation).flatMap
      (commandBits (rowValues input edge) (rowContext input edge)) =
      encodeWords (GraphTables.rowWords
        (Table.rowFromDart input (((edge, event), slot), orientation))) := by
  rw [rowCommands, List.flatMap_append, List.flatMap_append,
    affineCommands_bits, affineCommands_bits, bitCommands_bits, relationBits_values]
  have htail := Addresses.fieldForDartTail_eval input.vertices input.darts q edge
    input.rows[edge].tail input.rows[input.rows[edge].reverseIndex].tail event slot orientation
    (Relations.oldPredicate input.rows[edge].relation)
  have hreverse := Addresses.reverseDartField_eval input.vertices input.darts q edge
    event slot orientation input.rows[edge].tail.val
      input.rows[input.rows[edge].reverseIndex].tail.val
  let row := Table.rowFromDart input (((edge, event), slot), orientation)
  have tailEq : affineValue (Addresses.dartTailTerms q event slot orientation)
      (rowValues input edge) (Addresses.dartTailOffset q event slot orientation
        (Relations.oldPredicate (rowContext input edge).1)).val = row.tail.val := htail
  have reverseEq : affineValue (Addresses.reverseDartField q event slot orientation).terms
      (rowValues input edge) (Addresses.reverseDartField q event slot orientation).offset.val =
      row.reverseIndex.val := hreverse
  have relationEq : Relations.relationFromTable (rowContext input edge).1
      (rowContext input edge).2 event slot orientation = row.relation := rfl
  rw [encodedRow]
  have combined := congrArg₂ (fun a b : List Bool => a ++ b)
    (congrArg encodeWord tailEq)
    (congrArg₂ (fun a b : List Bool => a ++ b) (congrArg encodeWord reverseEq)
      (congrArg (fun relation => encodeWords (GraphTables.relationWords relation)) relationEq))
  simpa only [List.append_assoc] using combined

def blockCommands (q : Nat) : List (RowCommand q) :=
  (Enumeration.localEvents q).flatMap fun event =>
    (List.finRange 6).flatMap fun slot =>
      [false, true].flatMap fun orientation => rowCommands q event slot orientation

def blockWords {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) : List Nat :=
  (Enumeration.localEvents q).flatMap fun event =>
    (List.finRange 6).flatMap fun slot =>
      [false, true].flatMap fun orientation =>
        GraphTables.rowWords (Table.rowFromDart input (((edge, event), slot), orientation))

theorem tableWords_eq_blocks {q : Nat}
    (input : GenericGraphTables.Table q) :
    GraphTables.tableWords (Table.build input) =
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] ++
      (List.finRange input.darts).flatMap (blockWords input) := by
  rw [Table.tableWords_eq_ordered, Enumeration.ordered_dart]
  unfold blockWords
  simp only [List.flatMap_assoc, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

def headerCommands (q : Nat) (σ : Type) : List (Command 2 σ (Addresses.fieldBound q)) :=
  affineCommands [(0, Enumeration.tapeCount q),
      (1, Enumeration.localCount q + Enumeration.pairTapeCount q)]
      (fun _ => Addresses.zeroOffset q) ++
    affineCommands [(1, 12 * Enumeration.localCount q)] (fun _ => Addresses.zeroOffset q)

theorem headerCommands_bits {σ : Type} (q n m : Nat) (ambient : σ) :
    (headerCommands q σ).flatMap (commandBits ![n, m] ambient) =
      encodeWords [Enumeration.vertexCount n m q, Enumeration.dartCount m q] := by
  rw [headerCommands, List.flatMap_append, affineCommands_bits, affineCommands_bits]
  have vertices : affineValue
      [(0, Enumeration.tapeCount q), (1, Enumeration.localCount q + Enumeration.pairTapeCount q)]
      ![n, m] (Addresses.zeroOffset q).val = Enumeration.vertexCount n m q := by
    exact Addresses.headerVertices_eval q n m 0 0 0
  have darts : affineValue [(1, 12 * Enumeration.localCount q)] ![n, m]
      (Addresses.zeroOffset q).val = Enumeration.dartCount m q := by
    exact Addresses.headerDarts_eval q n m 0 0 0
  rw [vertices, darts]
  simp [encodeWords]

@[simp] theorem headerCommands_length (q : Nat) (σ : Type) :
    (headerCommands q σ).length = 7 := by
  simp [headerCommands, affineCommands_length]

def headerInTime {K Λ σ : Type} [DecidableEq K] (q n m : Nat)
    (sources : Fin 2 → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label (headerCommands q σ).length (Addresses.fieldBound q) → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement (listCommands (headerCommands q σ))
      sources scratch output labels exit label)
    (base : K → List Bool) (operands : ∀ i, base (sources i) = encodeWord (![n, m] i))
    (scratchEmpty : base scratch = []) (ambient : σ) (N : Nat) (hn : n ≤ N) (hm : m ≤ N) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (labelAt (headerCommands q σ).length (Addresses.fieldBound q) 0 .entry)),
        ((ambient, ()), none), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes output base
        (encodeWords [Enumeration.vertexCount n m q, Enumeration.dartCount m q])⟩)
      (7 * (3 * (N + 1) + 3) + 1) := by
  have bounded : ∀ i : Fin 2, ![n, m] i ≤ N := by
    intro i
    fin_cases i <;> simp [hn, hm]
  have run := planInTime (listCommands (headerCommands q σ)) sources scratch output
    sourceScratch sourceOutput scratchOutput labels exit p atLabels ![n, m] base operands
    scratchEmpty ambient N bounded
  rw [bits_listCommands, headerCommands_bits] at run
  simpa only [headerCommands_length] using run

theorem encodeWords_flatMap {α : Type} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun item => encodeWords (words item)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [encodeWords_append, ih]

theorem blockCommands_bits {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) :
    (blockCommands q).flatMap (commandBits (rowValues input edge) (rowContext input edge)) =
      encodeWords (blockWords input edge) := by
  simp only [blockCommands, blockWords, List.flatMap_assoc, encodeWords_flatMap,
    rowCommands_bits]

theorem rowCommands_length_le (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : (rowCommands q event slot orientation).length ≤ 4104 := by
  have htail := Addresses.dartTailTerms_length_le q event slot orientation
  simp only [rowCommands, List.length_append, affineCommands_length,
    Addresses.reverseDartField, List.length_cons, List.length_nil,
    bitCommands, List.length_map, relationBits, List.length_ofFn]
  omega

theorem flatMap_length_le {α β : Type} (items : List α) (f : α → List β)
    (bound : Nat) (bounded : ∀ item ∈ items, (f item).length ≤ bound) :
    (items.flatMap f).length ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons item items ih =>
    have hh := bounded item (by simp)
    have ht := ih (fun x hx => bounded x (by simp [hx]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

theorem blockCommands_length_le (q : Nat) :
    (blockCommands q).length ≤ Enumeration.localCount q * (6 * (2 * 4104)) := by
  unfold blockCommands
  apply le_trans (flatMap_length_le _ _ (6 * (2 * 4104)) ?_) (by simp)
  intro event _
  apply le_trans (flatMap_length_le _ _ (2 * 4104) ?_) (by simp)
  intro slot _
  apply le_trans (flatMap_length_le _ _ 4104 ?_) (by simp)
  intro orientation _
  exact rowCommands_length_le q event slot orientation

def blockInTime {K Λ : Type} [DecidableEq K] {q : Nat}
    (input : GenericGraphTables.Table q) (edge : Fin input.darts)
    (sources : Fin 5 → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label (blockCommands q).length (Addresses.fieldBound q) → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State (Context q)))
    (atLabels : ∀ label, p (labels label) = statement (listCommands (blockCommands q))
      sources scratch output labels exit label)
    (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (rowValues input edge i))
    (scratchEmpty : base scratch = []) (N : Nat)
    (bounded : ∀ i, rowValues input edge i ≤ N) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (labelAt (blockCommands q).length (Addresses.fieldBound q) 0 .entry)),
        ((rowContext input edge, ()), none), base⟩
      (some ⟨exit, ((rowContext input edge, ()), none),
        resultTapes output base (encodeWords (blockWords input edge))⟩)
      (Enumeration.localCount q * (6 * (2 * 4104)) * (3 * (N + 1) + 3) + 1) := by
  let run := planInTime (listCommands (blockCommands q)) sources scratch output sourceScratch
    sourceOutput scratchOutput labels exit p atLabels (rowValues input edge) base operands
    scratchEmpty (rowContext input edge) N bounded
  have hbits := bits_listCommands (blockCommands q) (rowValues input edge) (rowContext input edge)
  rw [blockCommands_bits] at hbits
  rw [hbits] at run
  exact { toEvalsTo := run.toEvalsTo, steps_le_m :=
    run.steps_le_m.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (blockCommands_length_le q)) 1) }

def blockCommandsIn {σ : Type} (q : Nat) (context : σ → Context q) :
    List (Command 5 σ (Addresses.fieldBound q)) :=
  (blockCommands q).map (fun command => command.mapAmbient context)

theorem blockCommandsIn_bits {σ : Type} {q : Nat}
    (input : GenericGraphTables.Table q) (edge : Fin input.darts)
    (context : σ → Context q) (ambient : σ) (hcontext : context ambient = rowContext input edge) :
    (blockCommandsIn q context).flatMap (commandBits (rowValues input edge) ambient) =
      encodeWords (blockWords input edge) := by
  simp only [blockCommandsIn, List.flatMap_map, commandBits_mapAmbient]
  rw [hcontext]
  exact blockCommands_bits input edge

def blockInTimeAmbient {K Λ σ : Type} [DecidableEq K] {q : Nat}
    (input : GenericGraphTables.Table q) (edge : Fin input.darts)
    (context : σ → Context q) (ambient : σ) (hcontext : context ambient = rowContext input edge)
    (sources : Fin 5 → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label (blockCommandsIn q context).length (Addresses.fieldBound q) → Λ)
    (exit : Option Λ) (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement (listCommands (blockCommandsIn q context))
      sources scratch output labels exit label)
    (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (rowValues input edge i))
    (scratchEmpty : base scratch = []) (N : Nat)
    (bounded : ∀ i, rowValues input edge i ≤ N) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (labelAt (blockCommandsIn q context).length (Addresses.fieldBound q) 0 .entry)),
        ((ambient, ()), none), base⟩
      (some ⟨exit, ((ambient, ()), none),
        resultTapes output base (encodeWords (blockWords input edge))⟩)
      (Enumeration.localCount q * (6 * (2 * 4104)) * (3 * (N + 1) + 3) + 1) := by
  have run := planInTime (listCommands (blockCommandsIn q context)) sources scratch output
    sourceScratch sourceOutput scratchOutput labels exit p atLabels (rowValues input edge)
    base operands scratchEmpty ambient N bounded
  rw [bits_listCommands, blockCommandsIn_bits input edge context ambient hcontext] at run
  have lengthBound : (blockCommandsIn q context).length ≤
      Enumeration.localCount q * (6 * (2 * 4104)) := by
    simpa only [blockCommandsIn, List.length_map] using blockCommands_length_le q
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  exact run.steps_le_m.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ lengthBound) 1)

end MinUncutGames.Foundations.PCP.AlphabetTable.EmitRows

namespace MinUncutGames.Foundations.PCP.AlphabetTable.Cleanup

open Turing
open Complexity
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (initial : σ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun _ => (initial, none))
    (match exit with | none => .halt | some label => .goto fun _ => label)

def instruction {n : Nat} (selected : Fin n → K) (labels : Fin (n + 1) → Λ)
    (initial : σ) (exit : Option Λ) (phase : Fin (n + 1)) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  if h : phase.val < n then
    MachineDrain.drain (selected ⟨phase.val, h⟩) (labels phase)
      (some (labels ⟨phase.val + 1, Nat.succ_lt_succ h⟩))
  else finish initial exit

omit [DecidableEq K] in
@[simp] theorem instruction_drain {n : Nat} (selected : Fin n → K)
    (labels : Fin (n + 1) → Λ) (initial : σ) (exit : Option Λ) (i : Fin n) :
    instruction selected labels initial exit i.castSucc =
      MachineDrain.drain (selected i) (labels i.castSucc) (some (labels i.succ)) := by
  simp [instruction, i.isLt]
  rfl

omit [DecidableEq K] in
@[simp] theorem instruction_finish {n : Nat} (selected : Fin n → K)
    (labels : Fin (n + 1) → Λ) (initial : σ) (exit : Option Λ) :
    instruction selected labels initial exit (Fin.last n) = finish initial exit := by
  simp [instruction]

def clearTapes : {n : Nat} → (Fin n → K) → (K → List Bool) → K → List Bool
  | 0, _, base => base
  | n + 1, selected, base =>
      clearTapes (fun i : Fin n => selected i.succ) (Function.update base (selected 0) [])

def actualCost : {n : Nat} → (Fin n → K) → (K → List Bool) → Nat
  | 0, _, _ => 1
  | n + 1, selected, base =>
      actualCost (fun i : Fin n => selected i.succ) (Function.update base (selected 0) []) +
        ((base (selected 0)).length + 1)

theorem clearTapes_apply {n : Nat} (selected : Fin n → K) (base : K → List Bool) (k : K) :
    clearTapes selected base k = if ∃ i, selected i = k then [] else base k := by
  induction n generalizing base with
  | zero => simp [clearTapes]
  | succ n ih =>
      rw [clearTapes, ih]
      by_cases first : selected 0 = k
      · subst k
        simp [Function.update]
      · have notFirst : k ≠ selected 0 := Ne.symm first
        by_cases later : ∃ i : Fin n, selected i.succ = k <;>
          simp [Fin.exists_fin_succ, first, later, Function.update, notFirst]

@[simp] theorem clearTapes_selected {n : Nat} (selected : Fin n → K)
    (base : K → List Bool) (i : Fin n) : clearTapes selected base (selected i) = [] := by
  rw [clearTapes_apply, ite_eq_left ⟨i, rfl⟩]

theorem clearTapes_unselected {n : Nat} (selected : Fin n → K)
    (base : K → List Bool) (k : K) (notSelected : ∀ i, selected i ≠ k) :
    clearTapes selected base k = base k := by
  rw [clearTapes_apply]
  simp [notSelected]

theorem actualCost_le {n : Nat} (selected : Fin n → K) (base : K → List Bool) :
    actualCost selected base ≤ (∑ i, (base (selected i)).length) + n + 1 := by
  induction n generalizing base with
  | zero => simp [actualCost]
  | succ n ih =>
      have tailBound := ih (fun i : Fin n => selected i.succ)
        (Function.update base (selected 0) [])
      have sumBound :
          (∑ i : Fin n, ((Function.update base (selected 0) []) (selected i.succ)).length) ≤
            ∑ i : Fin n, (base (selected i.succ)).length := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : selected i.succ = selected 0 <;> simp [h]
      rw [actualCost, Fin.sum_univ_succ]
      omega

theorem cleanupTrace {n : Nat} (selected : Fin n → K) (labels : Fin (n + 1) → Λ)
    (initial : σ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : ∀ i : Fin n, program (labels i.castSucc) =
      MachineDrain.drain (selected i) (labels i.castSucc) (some (labels i.succ)))
    (atFinish : program (labels (Fin.last n)) = finish initial exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[actualCost selected base]
      (some ⟨some (labels 0), (ambient, register), base⟩) =
      some ⟨exit, (initial, none), clearTapes selected base⟩ := by
  induction n generalizing base ambient register with
  | zero =>
      change some (TM2.stepAux (program (labels 0)) (ambient, register) base) = _
      rw [show program (labels 0) = finish initial exit from atFinish]
      cases exit <;> rfl
  | succ n ih =>
      rw [actualCost, Function.iterate_add_apply]
      have first := MachineDrain.drainTrace (selected 0) (labels (0 : Fin (n + 1)).castSucc)
        (some (labels (0 : Fin (n + 1)).succ)) program (atDrain 0)
        base (base (selected 0)) ambient register
      simp only [Function.update_eq_self, Fin.castSucc_zero] at first
      rw [first]
      exact ih (fun i : Fin n => selected i.succ) (fun i => labels i.succ)
        (fun i => atDrain i.succ) atFinish (Function.update base (selected 0) []) ambient none

def cleanupInTime {n : Nat} (selected : Fin n → K) (labels : Fin (n + 1) → Λ)
    (initial : σ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : ∀ i : Fin n, program (labels i.castSucc) =
      MachineDrain.drain (selected i) (labels i.castSucc) (some (labels i.succ)))
    (atFinish : program (labels (Fin.last n)) = finish initial exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels 0), (ambient, register), base⟩
      (some ⟨exit, (initial, none), clearTapes selected base⟩)
      ((∑ i, (base (selected i)).length) + n + 1) where
  steps := actualCost selected base
  evals_in_steps := cleanupTrace selected labels initial exit program atDrain atFinish
    base ambient register
  steps_le_m := actualCost_le selected base

def program {n : Nat} (selected : Fin n → K) (initial : σ) :
    Fin (n + 1) → TM2.Stmt (Alphabet (K := K)) (Fin (n + 1)) (σ × Option Bool) :=
  instruction selected id initial none

def machine [Fintype K] [Fintype σ] {n : Nat} (selected : Fin n → K)
    (input output : K) (initial : σ) : FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ := Alphabet
  Λ := Fin (n + 1)
  main := 0
  σ := σ × Option Bool
  initialState := (initial, none)
  m := program selected initial

def machineInTime [Fintype K] [Fintype σ] {n : Nat} (selected : Fin n → K)
    (input output : K) (initial : σ) (base : K → List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine selected input output initial).step
      ⟨some (0 : Fin (n + 1)), (ambient, register), base⟩
      (some ⟨none, (initial, none), clearTapes selected base⟩)
      ((∑ i, (base (selected i)).length) + n + 1) :=
  cleanupInTime selected id initial none (program selected initial)
    (fun i => instruction_drain selected id initial none i)
    (instruction_finish selected id initial none) base ambient register

theorem clearTapes_outputOnly {n : Nat} (selected : Fin n → K)
    (output : K) (base : K → List Bool)
    (excludesOutput : ∀ i, selected i ≠ output)
    (coversOther : ∀ k, k ≠ output → ∃ i, selected i = k) :
    clearTapes selected base = fun k => if k = output then base output else [] := by
  funext k
  by_cases h : k = output
  · subst k
    simp [clearTapes_unselected selected base output excludesOutput]
  · rw [clearTapes_apply]
    simp [h, coversOther k h]

def machineHaltInTime [Fintype K] [Fintype σ] {n : Nat} (selected : Fin n → K)
    (input output : K) (initial : σ) (base : K → List Bool)
    (ambient : σ) (register : Option Bool)
    (excludesOutput : ∀ i, selected i ≠ output)
    (coversOther : ∀ k, k ≠ output → ∃ i, selected i = k) :
    StateTransition.EvalsToInTime (machine selected input output initial).step
      ⟨some (0 : Fin (n + 1)), (ambient, register), base⟩
      (some (haltList (machine selected input output initial) (base output)))
      ((∑ i, (base (selected i)).length) + n + 1) := by
  have tapeEq := clearTapes_outputOnly selected output base excludesOutput coversOther
  have haltEq : (⟨none, (initial, none), clearTapes selected base⟩ :
      (machine selected input output initial).Cfg) =
      haltList (machine selected input output initial) (base output) := by
    congr 1
  rw [← haltEq]
  exact machineInTime selected input output initial base ambient register

end MinUncutGames.Foundations.PCP.AlphabetTable.Cleanup

end OAI
