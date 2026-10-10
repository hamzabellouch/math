import Mathlib
import OAI.Computability.DirectedFeedback.Encoding.CompareLoop

namespace OAI


namespace DFVSGames.Foundations.PCP.AlphabetTable.EmitRows

open Turing
open DFVSGames.Foundations.Complexity
open Emitter

abbrev Context (q : Nat) := Vector Bool (q * q) × Bool
abbrev RowCommand (q : Nat) := Command 5 (Context q) (Addresses.fieldBound q)

def relationBits (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : List (Context q → Bool) :=
  List.ofFn fun index : Fin 4096 => fun context =>
    (Relations.relationFromTable context.1 context.2 event slot orientation)[index]

private theorem vector_list_ofFn_inline_EmitRows {α : Type} {n : Nat} (vector : Vector α n) :
    List.ofFn (fun index : Fin n => vector[index]) = vector.toList := by
  have equality := congrArg Vector.toList (Vector.ofFn_getElem (xs := vector))
  simpa only [Vector.toList_ofFn, Fin.getElem_fin] using equality

private theorem bitValues_ofFn_inline_EmitRows {σ : Type} {n : Nat}
    (relation : σ → Vector Bool n) (context : σ) :
    (List.ofFn (fun index : Fin n => fun state => (relation state)[index])).map
      (fun bit => if bit context then 1 else 0) =
      (relation context).toList.map GraphTables.bitWord := by
  rw [← vector_list_ofFn_inline_EmitRows (relation context)]
  simp only [List.map_ofFn]
  rfl

theorem relationBits_values (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) (context : Context q) :
    (relationBits q event slot orientation).map (fun bit => if bit context then 1 else 0) =
      GraphTables.relationWords
        (Relations.relationFromTable context.1 context.2 event slot orientation) := by
  exact bitValues_ofFn_inline_EmitRows (fun state : Context q =>
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

private theorem encodedRow_inline_EmitRows {n m : Nat} (row : GraphTables.DartRow n m) :
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
  rw [encodedRow_inline_EmitRows]
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

private theorem encodeWords_flatMap_inline_EmitRows {α : Type} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun item => encodeWords (words item)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [encodeWords_append, ih]

theorem blockCommands_bits {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) :
    (blockCommands q).flatMap (commandBits (rowValues input edge) (rowContext input edge)) =
      encodeWords (blockWords input edge) := by
  simp only [blockCommands, blockWords, List.flatMap_assoc, encodeWords_flatMap_inline_EmitRows,
    rowCommands_bits]

theorem rowCommands_length_le (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : (rowCommands q event slot orientation).length ≤ 4104 := by
  have htail := Addresses.dartTailTerms_length_le q event slot orientation
  simp only [rowCommands, List.length_append, affineCommands_length,
    Addresses.reverseDartField, List.length_cons, List.length_nil,
    bitCommands, List.length_map, relationBits, List.length_ofFn]
  omega

private theorem flatMap_length_le_inline_EmitRows {α β : Type} (items : List α) (f : α → List β)
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
  apply le_trans (flatMap_length_le_inline_EmitRows _ _ (6 * (2 * 4104)) ?_) (by simp)
  intro event _
  apply le_trans (flatMap_length_le_inline_EmitRows _ _ (2 * 4104) ?_) (by simp)
  intro slot _
  apply le_trans (flatMap_length_le_inline_EmitRows _ _ 4104 ?_) (by simp)
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

end DFVSGames.Foundations.PCP.AlphabetTable.EmitRows


namespace DFVSGames.Foundations.PCP.AlphabetTable.Cleanup

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

end DFVSGames.Foundations.PCP.AlphabetTable.Cleanup


namespace DFVSGames.Foundations.PCP.AlphabetTable.Driver

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open RuntimeModel

def headerPlan (q : Nat) := EmitRows.headerCommands q (Ambient q)
def rowPlan (q : Nat) := EmitRows.blockCommandsIn q (@context q)

inductive Label (q : Nat)
  | setup (label : Setup.Label)
  | header (label : Emitter.Label (headerPlan q).length (Addresses.fieldBound q))
  | guard | tailStart | tailLoop | reverseStart | reverseLoop | readPredicate
  | headCopyFirst | headCopySecond | indexCopyFirst | indexCopySecond
  | headVertices | headDarts | headLookup (label : Lookup.Label)
  | compare (label : CompareLoop.Label)
  | emit (label : Emitter.Label (rowPlan q).length (Addresses.fieldBound q))
  | clearField (slot : Fin 3)
  | increment | reverseOutput | cleanup (slot : Fin 16)
  deriving DecidableEq, Fintype

def headerEntry (q : Nat) : Label q :=
  .header (Emitter.labelAt (headerPlan q).length (Addresses.fieldBound q) 0 .entry)

def rowEntry (q : Nat) : Label q :=
  .emit (Emitter.labelAt (rowPlan q).length (Addresses.fieldBound q) 0 .entry)

def clearNext {q : Nat} (slot : Fin 3) : Label q :=
  if h : slot.val < 2 then .clearField ⟨slot.val + 1, by omega⟩ else .increment

def program (q : Nat) : Label q → TM2.Stmt Alphabet (Label q) (State q)
  | .setup label => Setup.statement setupPorts Label.setup (some (headerEntry q)) label
  | .header label => emitterStatement
      (Emitter.statement (Emitter.listCommands (headerPlan q)) headerSources .scratch .reversed
        Label.header (some .guard) label)
  | .guard => MachineUnaryCounter.guard .counter .tailStart .reverseOutput
  | .tailStart => SourceMachine.fieldStart .tail .tailLoop
  | .tailLoop => SourceMachine.fieldLoop .cursor .tail .tailLoop (some .reverseStart)
  | .reverseStart => SourceMachine.fieldStart .reverseIndex .reverseLoop
  | .reverseLoop => SourceMachine.fieldLoop .cursor .reverseIndex .reverseLoop (some .readPredicate)
  | .readPredicate => ReadRelation.parser .cursor .headCopyFirst
  | .headCopyFirst => Reduction.MachineTransfer.loopAt .original .scratch id false
      .headCopyFirst (some .headCopySecond)
  | .headCopySecond => MachineCopy.forkLoop .scratch .original .scan false
      .headCopySecond (some .indexCopyFirst)
  | .indexCopyFirst => Reduction.MachineTransfer.loopAt .reverseIndex .scratch id false
      .indexCopyFirst (some .indexCopySecond)
  | .indexCopySecond => MachineCopy.forkLoop .scratch .reverseIndex .indexScan false
      .indexCopySecond (some .headVertices)
  | .headVertices => MachineLookup.discard .scan .headVertices .headDarts
  | .headDarts => MachineLookup.discard .scan .headDarts (.headLookup .guard)
  | .headLookup label => Lookup.statement q .indexScan .scan .head Label.headLookup
      (some (.compare .leftFirst)) label
  | .compare label => CompareLoop.statement Label.compare (rowEntry q) label
  | .emit label => emitterStatement
      (Emitter.statement (Emitter.listCommands (rowPlan q)) rowSources .scratch .reversed
        Label.emit (some (.clearField 0)) label)
  | .clearField slot => MachineDrain.drain (fieldPorts slot) (.clearField slot)
      (some (clearNext slot))
  | .increment => nextRow .guard
  | .reverseOutput => Reduction.MachineTransfer.loopAt .reversed .output id false
      .reverseOutput (some (.cleanup 0))
  | .cleanup slot => Cleanup.instruction cleanupPorts Label.cleanup (initial q).1 none slot

def machine (q : Nat) : FinTM2 := by
  letI := ReadRelation.stateFintype Flags q
  exact {
    K := Tape
    k₀ := .original
    k₁ := .output
    Γ := Alphabet
    Λ := Label q
    main := .setup .copyFirst
    σ := State q
    initialState := initial q
    m := program q }

@[simp] theorem program_setup (q : Nat) (label : Setup.Label) :
    program q (.setup label) =
      Setup.statement setupPorts Label.setup (some (headerEntry q)) label := rfl

@[simp] theorem program_guard (q : Nat) : program q .guard =
    MachineUnaryCounter.guard .counter .tailStart .reverseOutput := rfl

@[simp] theorem program_headLookup (q : Nat) (label : Lookup.Label) :
    program q (.headLookup label) = Lookup.statement q .indexScan .scan .head
      Label.headLookup (some (.compare .leftFirst)) label := rfl

@[simp] theorem program_compare (q : Nat) (label : CompareLoop.Label) :
    program q (.compare label) = CompareLoop.statement Label.compare (rowEntry q) label := rfl

@[simp] theorem program_increment (q : Nat) : program q .increment = nextRow .guard := rfl

end DFVSGames.Foundations.PCP.AlphabetTable.Driver


namespace DFVSGames.Foundations.PCP.AlphabetTable.LoopState

open DFVSGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def inputBits (input : GenericGraphTables.Table q) : List Bool :=
  GenericGraphTables.tableBits input

def prefixWords (input : GenericGraphTables.Table q) (e : Nat) : List Nat :=
  [Enumeration.vertexCount input.vertices input.darts q,
    Enumeration.dartCount input.darts q] ++
    ((List.finRange input.darts).take e).flatMap (EmitRows.blockWords input)

def prefixBits (input : GenericGraphTables.Table q) (e : Nat) : List Bool :=
  encodeWords (prefixWords input e)

def cursorWords (input : GenericGraphTables.Table q) (e : Nat) : List Nat :=
  ((GenericGraphTables.rowList input).drop e).flatMap GenericGraphTables.rowWords

def cursorBits (input : GenericGraphTables.Table q) (e : Nat) : List Bool :=
  encodeWords (cursorWords input e)

@[simp] theorem prefixWords_zero (input : GenericGraphTables.Table q) :
    prefixWords input 0 =
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] := by
  simp [prefixWords]

@[simp] theorem prefixBits_zero (input : GenericGraphTables.Table q) :
    prefixBits input 0 = encodeWords
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] := by
  rw [prefixBits, prefixWords_zero]

theorem prefixWords_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    prefixWords input (e + 1) =
      prefixWords input e ++ EmitRows.blockWords input ⟨e, he⟩ := by
  have bound : e < (List.finRange input.darts).length := by simpa using he
  have take := List.take_succ_eq_append_getElem bound
  have atIndex : (List.finRange input.darts)[e]'bound = (⟨e, he⟩ : Fin input.darts) := by
    simp
  rw [atIndex] at take
  unfold prefixWords
  rw [take, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem prefixBits_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    prefixBits input (e + 1) =
      prefixBits input e ++ encodeWords (EmitRows.blockWords input ⟨e, he⟩) := by
  rw [prefixBits, prefixWords_succ input e he, encodeWords_append]
  rfl

theorem prefixBits_reverse_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    (prefixBits input (e + 1)).reverse =
      (encodeWords (EmitRows.blockWords input ⟨e, he⟩)).reverse ++
        (prefixBits input e).reverse := by
  rw [prefixBits_succ input e he, List.reverse_append]

theorem prefixWords_full (input : GenericGraphTables.Table q) :
    prefixWords input input.darts = GraphTables.tableWords (Table.build input) := by
  have allRows : (List.finRange input.darts).take input.darts = List.finRange input.darts := by
    apply List.take_of_length_le
    simp
  unfold prefixWords
  rw [allRows]
  exact (EmitRows.tableWords_eq_blocks input).symm

theorem prefixBits_full (input : GenericGraphTables.Table q) :
    prefixBits input input.darts = GraphTables.tableBits (Table.build input) := by
  rw [prefixBits, prefixWords_full]
  rfl

@[simp] theorem cursorBits_zero (input : GenericGraphTables.Table q) :
    cursorBits input 0 =
      encodeWords ((GenericGraphTables.rowList input).flatMap GenericGraphTables.rowWords) := by
  simp [cursorBits, cursorWords]

theorem cursorWords_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    cursorWords input e =
      GenericGraphTables.rowWords input.rows[(⟨e, he⟩ : Fin input.darts)] ++
      cursorWords input (e + 1) := by
  have bound : e < (GenericGraphTables.rowList input).length := by
    simpa only [GenericGraphTables.rowList_length] using he
  unfold cursorWords
  rw [List.drop_eq_getElem_cons bound, List.flatMap_cons]
  simp only [GenericGraphTables.rowList, Vector.getElem_toList, Fin.getElem_fin]

theorem cursorBits_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    cursorBits input e =
      encodeWords (GenericGraphTables.rowWords input.rows[(⟨e, he⟩ : Fin input.darts)]) ++
      cursorBits input (e + 1) := by
  rw [cursorBits, cursorWords_succ input e he, encodeWords_append]
  rfl

@[simp] theorem cursorBits_full (input : GenericGraphTables.Table q) :
    cursorBits input input.darts = [] := by
  have finished := List.drop_length (l := GenericGraphTables.rowList input)
  rw [GenericGraphTables.rowList_length] at finished
  unfold cursorBits cursorWords
  rw [finished]
  rfl

structure Ready (input : GenericGraphTables.Table q) (e : Nat)
    (base : Tape → List Bool) : Prop where
  le_darts : e ≤ input.darts
  original : base .original = inputBits input
  cursor : base .cursor = cursorBits input e
  vertices : base .vertices = encodeWord input.vertices
  darts : base .darts = encodeWord input.darts
  counter : base .counter = encodeWord (input.darts - e)
  edge : base .edge = encodeWord e
  tail : base .tail = []
  reverseIndex : base .reverseIndex = []
  head : base .head = []
  scratch : base .scratch = []
  compareLeft : base .compareLeft = []
  compareRight : base .compareRight = []
  output : base .output = []
  reversed : base .reversed = (prefixBits input e).reverse

theorem Ready.of_agree {input : GenericGraphTables.Table q} {e : Nat}
    {base next : Tape → List Bool} (ready : Ready input e base)
    (agree : ∀ tape, tape ≠ .scan → tape ≠ .indexScan → next tape = base tape) :
    Ready input e next where
  le_darts := ready.le_darts
  original := (agree .original (by decide) (by decide)).trans ready.original
  cursor := (agree .cursor (by decide) (by decide)).trans ready.cursor
  vertices := (agree .vertices (by decide) (by decide)).trans ready.vertices
  darts := (agree .darts (by decide) (by decide)).trans ready.darts
  counter := (agree .counter (by decide) (by decide)).trans ready.counter
  edge := (agree .edge (by decide) (by decide)).trans ready.edge
  tail := (agree .tail (by decide) (by decide)).trans ready.tail
  reverseIndex := (agree .reverseIndex (by decide) (by decide)).trans ready.reverseIndex
  head := (agree .head (by decide) (by decide)).trans ready.head
  scratch := (agree .scratch (by decide) (by decide)).trans ready.scratch
  compareLeft := (agree .compareLeft (by decide) (by decide)).trans ready.compareLeft
  compareRight := (agree .compareRight (by decide) (by decide)).trans ready.compareRight
  output := (agree .output (by decide) (by decide)).trans ready.output
  reversed := (agree .reversed (by decide) (by decide)).trans ready.reversed

theorem Ready.update_scan {input : GenericGraphTables.Table q} {e : Nat}
    {base : Tape → List Bool} (ready : Ready input e base) (word : List Bool) :
    Ready input e (Function.update base .scan word) := by
  apply ready.of_agree
  intro tape notScan _
  simp [notScan]

theorem Ready.update_indexScan {input : GenericGraphTables.Table q} {e : Nat}
    {base : Tape → List Bool} (ready : Ready input e base) (word : List Bool) :
    Ready input e (Function.update base .indexScan word) := by
  apply ready.of_agree
  intro tape _ notIndexScan
  simp [notIndexScan]

theorem Ready.counter_succ {input : GenericGraphTables.Table q} {e : Nat}
    {base : Tape → List Bool} (ready : Ready input e base) (he : e < input.darts) :
    base .counter = encodeWord (input.darts - (e + 1) + 1) := by
  rw [ready.counter]
  congr 1
  omega

theorem Ready.counter_at_end {input : GenericGraphTables.Table q}
    {base : Tape → List Bool} (ready : Ready input input.darts base) :
    base .counter = encodeWord 0 := by
  simpa only [Nat.sub_self] using ready.counter

theorem Ready.cursor_at_end {input : GenericGraphTables.Table q}
    {base : Tape → List Bool} (ready : Ready input input.darts base) :
    base .cursor = [] := ready.cursor.trans (cursorBits_full input)

theorem Ready.reversed_at_end {input : GenericGraphTables.Table q}
    {base : Tape → List Bool} (ready : Ready input input.darts base) :
    base .reversed = (GraphTables.tableBits (Table.build input)).reverse := by
  rw [ready.reversed, prefixBits_full]

end DFVSGames.Foundations.PCP.AlphabetTable.LoopState

end OAI
