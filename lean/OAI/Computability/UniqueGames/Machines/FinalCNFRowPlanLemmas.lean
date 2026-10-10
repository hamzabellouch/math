import OAI.Computability.UniqueGames.Machines.FinalCNFMachineLemmas
import OAI.Computability.UniqueGames.Machines.FinalCNFPattern
import OAI.Computability.UniqueGames.Machines.FinalCNFTableAdapter
import OAI.Computability.UniqueGames.Machines.FinalCNFTemplate

namespace OAI


/-!
The fixed finite emission plan for one directed graph row. All choices based
on the relation are functions of its 4096-bit finite register. Vertex counts,
endpoint names and row indices are read by preserving unary scans.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable

section Templates

open FinalCNFTemplate

def referenceValue (vertices tail head row pattern : Nat) : Reference → Nat
  | .query i => if i.val < 6 then 6 * tail + i.val else 6 * head + (i.val - 6)
  | .auxiliary j => 6 * vertices + 36864 * row + (9 * pattern + j.val)

def auxiliaryFlag : Reference → Bool
  | .query _ => false
  | .auxiliary _ => true

def tailFlag : Reference → Bool
  | .query i => decide (i.val < 6)
  | .auxiliary _ => false

def headFlag : Reference → Bool
  | .query i => decide (6 ≤ i.val)
  | .auxiliary _ => false

theorem pattern_lt (p : VerifierToCNF.PatternIndex 12) : p.val < 4096 := by
  have hlen : (VerifierToCNF.patterns 12).length = 4096 := VerifierToCNF.patterns_length 12
  exact lt_of_lt_of_eq p.isLt hlen

def referenceOffset (p : VerifierToCNF.PatternIndex 12) : Reference → Fin 36864
  | .query i => ⟨if i.val < 6 then i.val else i.val - 6, by split <;> omega⟩
  | .auxiliary j => ⟨9 * p.val + j.val, by have hp := pattern_lt p; omega⟩

/-- Seven real commands for the two unary fields of a literal. -/
def literalPlan (p : VerifierToCNF.PatternIndex 12) (literal : Ambient → LiteralTemplate) : Plan :=
  [.scaledIf 0 6 (fun state => auxiliaryFlag (literal state).reference),
   .scaledIf 2 6 (fun state => tailFlag (literal state).reference),
   .scaledIf 3 6 (fun state => headFlag (literal state).reference),
   .scaledIf 4 36864 (fun state => auxiliaryFlag (literal state).reference),
   .bounded (fun state => referenceOffset p (literal state).reference),
   .literal [false],
   .bit (fun state => (literal state).positive)]

theorem literalPlan_length (p : VerifierToCNF.PatternIndex 12)
    (literal : Ambient → LiteralTemplate) : (literalPlan p literal).length = 7 := rfl

theorem literalPlan_bits (p : VerifierToCNF.PatternIndex 12)
    (literal : Ambient → LiteralTemplate) (vertices darts tail head row : Nat)
    (ambient : Ambient) :
    (literalPlan p literal).flatMap
      (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords (FinalCNFTemplate.literalWords
        (referenceValue vertices tail head row p.val) (literal ambient)) := by
  rcases h : literal ambient with ⟨reference, positive⟩
  cases reference with
  | query i =>
      by_cases hi : i.val < 6
      · simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
          referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
          hi, show ¬ 6 ≤ i.val by omega, encodeWords, encodeWord, List.replicate_add,
          List.append_assoc, -List.replicate_append_replicate]
        rfl
      · simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
          referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
          hi, show 6 ≤ i.val by omega, encodeWords, encodeWord, List.replicate_add,
          List.append_assoc, -List.replicate_append_replicate]
        rfl
  | auxiliary j =>
      simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
        referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
        encodeWords, encodeWord, List.replicate_add, List.append_assoc,
        -List.replicate_append_replicate]
      rfl

def patternLiteral (p : VerifierToCNF.PatternIndex 12) (clause : Fin 10) (slot : Fin 3)
    (ambient : Ambient) : LiteralTemplate :=
  literalAt (ambient.2 (FinalCNFPattern.patternRelationIndex p))
    (VerifierToCNF.patternAt 12 p) clause slot

def patternPlan (p : VerifierToCNF.PatternIndex 12) : Plan :=
  (List.finRange 10).flatMap fun clause =>
    (List.finRange 3).flatMap fun slot => literalPlan p (patternLiteral p clause slot)

def rowPlan : Plan :=
  (List.finRange (VerifierToCNF.patterns 12).length).flatMap patternPlan

theorem patternPlan_length (p : VerifierToCNF.PatternIndex 12) :
    (patternPlan p).length = 210 := by
  unfold patternPlan
  rw [VerifierToCNF.length_flatMap_constant _ _ 21]
  · simp
  · intro clause hclause
    rw [VerifierToCNF.length_flatMap_constant _ _ 7]
    · simp
    · intro slot hslot
      exact literalPlan_length _ _

theorem rowPlan_length : rowPlan.length = 860160 := by
  unfold rowPlan
  rw [VerifierToCNF.length_flatMap_constant _ _ 210]
  · rw [List.length_finRange, VerifierToCNF.patterns_length]
    norm_num
  · intro p hp
    exact patternPlan_length p

theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem patternPlan_bits (p : VerifierToCNF.PatternIndex 12)
    (vertices darts tail head row : Nat) (ambient : Ambient) :
    (patternPlan p).flatMap
      (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords (FinalCNFTemplate.words
        (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p) (referenceValue vertices tail head row p.val)) := by
  unfold patternPlan
  simp only [List.flatMap_assoc]
  simp_rw [literalPlan_bits]
  have hclauses :
      (List.finRange 10).map
        (fun c => (blockTemplates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
          (VerifierToCNF.patternAt 12 p))[c]) =
      templates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p) := by
    rw [← List.ofFn_eq_map]
    change List.ofFn (fun c : Fin 10 =>
      (blockTemplates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p))[c.val]) = _
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
    rfl
  unfold FinalCNFTemplate.words
  rw [← hclauses, List.flatMap_map, encodeWords_flatMap]
  apply List.flatMap_congr
  intro clause hclause
  simp only [List.finRange, List.ofFn_succ, List.ofFn_zero, List.flatMap_cons,
    List.flatMap_nil, patternLiteral, literalAt, FinalCNFTemplate.clauseWords,
    encodeWords_append, List.append_nil, List.append_assoc]
  rfl

theorem referenceValue_eq_resolve (table : GraphTables.Table) (e : Fin table.darts)
    (p : VerifierToCNF.PatternIndex 12) (reference : Reference) :
    referenceValue table.vertices table.rows[e].tail.val
      table.rows[table.rows[e].reverseIndex].tail.val e.val p.val reference =
      (resolve (FinalCNFPattern.tableVerifier table) e p reference).val := by
  cases reference with
  | query i =>
      rw [resolve_query_value]
      refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
      · rw [FinalBooleanVerifier.query_tail]
        simp only [referenceValue, Fin.val_castAdd, j.isLt, ite_true]
        change 6 * table.rows[e].tail.val + j.val = j.val + 6 * table.rows[e].tail.val
        omega
      · rw [FinalBooleanVerifier.query_head]
        simp only [referenceValue, Fin.val_natAdd]
        split
        · omega
        · change 6 * table.rows[table.rows[e].reverseIndex].tail.val +
              (6 + j.val - 6) = j.val + 6 * table.rows[table.rows[e].reverseIndex].tail.val
          omega
  | auxiliary j =>
      rw [resolve_auxiliary_value]
      change 6 * table.vertices + 36864 * e.val + (9 * p.val + j.val) =
        table.vertices * 6 + ((e.val * 4096 + p.val) * 9 + j.val)
      omega

theorem rowPlan_bits (table : GraphTables.Table) (e : Fin table.darts) :
    rowPlan.flatMap (Emitter.commandBits
      (values table.vertices table.darts table.rows[e].tail.val
        table.rows[table.rows[e].reverseIndex].tail.val e.val)
      ((), fun i => table.rows[e].relation[i])) =
      encodeWords ((VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
        (by decide) e).flatMap Complexity.clauseWords) := by
  unfold rowPlan VerifierToCNF.eventBlock
  simp only [List.flatMap_assoc]
  rw [encodeWords_flatMap]
  apply List.flatMap_congr
  intro p hp
  rw [patternPlan_bits]
  dsimp only
  rw [FinalCNFPattern.pattern_lookup_eq_verifier_accepts]
  have href := funext (referenceValue_eq_resolve table e p)
  rw [href]
  exact congrArg encodeWords (words_eq_block (FinalCNFPattern.tableVerifier table) e p)

end Templates

/-!
Actual finite-machine execution of the final converter's row phases. These
certificates use the concrete program statements, preserve all other tapes,
and expose the precise concatenated output of the fixed emission plan.
-/

open Turing

def endpointTapes (base : Tape → List Bool) (tail reverse : Nat) (rest : List Bool) :=
  Hastad.SourceMachine.fieldTapes Tape.input Tape.reverseIndex
    (Hastad.SourceMachine.fieldTapes Tape.input Tape.tail base
      (encodeWord reverse ++ rest) (encodeWord tail ++ base .tail))
    rest (encodeWord reverse ++ base .reverseIndex)

/-- Read the two fields actually stored in a graph row: tail and reverse dart. -/
def endpointsInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (tail reverse : Nat) (rest : List Bool)
    (hinput : base .input = encodeWord tail ++ encodeWord reverse ++ rest)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .startTail, ((ambient, ()), none), base⟩
      (some ⟨some .headTableFirst, ((ambient, ()), none),
        endpointTapes base tail reverse rest⟩) (tail + reverse + 4) := by
  let first := Hastad.SourceMachine.fieldTapes Tape.input Tape.tail base
    (encodeWord reverse ++ rest) (encodeWord tail ++ base .tail)
  let run₁ := Hastad.SourceMachine.fieldInTime Tape.input Tape.tail (by decide)
    .startTail .readTail (some .startReverse) (program headerPlan plan) rfl rfl
    base tail (encodeWord reverse ++ rest) (by simpa only [List.append_assoc] using hinput)
    (ambient, ()) none
  have input₁ : first .input = encodeWord reverse ++ rest := by
    simp [first, Hastad.SourceMachine.fieldTapes]
  have reverse₁ : first .reverseIndex = base .reverseIndex := by
    simp [first, Hastad.SourceMachine.fieldTapes]
  let run₂ := Hastad.SourceMachine.fieldInTime Tape.input Tape.reverseIndex (by decide)
    .startReverse .readReverse (some .headTableFirst) (program headerPlan plan) rfl rfl
    first reverse rest input₁ (ambient, ()) none
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  simpa only [first, reverse₁, endpointTapes, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using joined

/-- The fixed unary relation reader occupies one finite TM2 statement. -/
def relationInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (relation : GraphTables.RelationTable) (rest : List Bool)
    (hinput : base .input = encodeWords (GraphTables.relationWords relation) ++ rest)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .readRelation, ((ambient, ()), none), base⟩
      (some ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((((), fun i => relation[i]), ()), none), Function.update base .input rest⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .readRelation) _ _) = _
    rw [program, stepAux_readRelationAt _ _ _ _ _ _ _ _ _ hinput]
  steps_le_m := Nat.le_refl _

/-- Execute the complete fixed row emission plan against physical unary tapes. -/
def emitInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (operands : Fin 5 → Nat) (hoperands : ∀ i, base (source i) = encodeWord (operands i))
    (hscratch : base .scratch = []) (ambient : Ambient)
    (N : Nat) (hbounded : ∀ i, operands i ≤ N) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((ambient, ()), none), base⟩
      (some ⟨some .clearTail, ((ambient, ()), none),
        Function.update base .accumulator
          ((plan.flatMap (Emitter.commandBits operands ambient)).reverse ++ base .accumulator)⟩)
      (plan.length * (3 * (N + 1) + 3) + 1) := by
  have run := Emitter.planInTime (Emitter.listCommands plan)
    source Tape.scratch Tape.accumulator source_ne_scratch source_ne_accumulator (by decide)
    Label.row (some .clearTail) (program headerPlan plan) (fun _ => rfl)
    operands base hoperands hscratch ambient N hbounded
  simpa only [Emitter.bits_listCommands, Emitter.resultTapes] using run

def finishTapes (base : Tape → List Bool) (row : Nat) : Tape → List Bool :=
  Function.update
    (Function.update (Function.update (Function.update base Tape.tail []) Tape.head [])
      Tape.reverseIndex []) Tape.rowIndex (encodeWord (row + 1))

/-- Clear precisely the three isolated temporary fields and increment the
physical row counter before returning to the input guard. -/
def finishInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (tail head reverse row : Nat)
    (htail : base .tail = encodeWord tail) (hhead : base .head = encodeWord head)
    (hreverse : base .reverseIndex = encodeWord reverse)
    (hrow : base .rowIndex = encodeWord row) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .clearTail, ((ambient, ()), none), base⟩
      (some ⟨some .guard, ((ambient, ()), none), finishTapes base row⟩)
      (tail + head + reverse + 4) := by
  let t₁ := Function.update base Tape.tail []
  let t₂ := Function.update t₁ Tape.head []
  let t₃ := Function.update t₂ Tape.reverseIndex []
  let run₁ := MachineLookup.discardInTime Tape.tail .clearTail .clearHead
    (program headerPlan plan) rfl base tail [] (by simpa using htail) (ambient, ()) none
  have hhead₁ : t₁ .head = encodeWord head := by simp [t₁, hhead]
  let run₂ := MachineLookup.discardInTime Tape.head .clearHead .clearReverse
    (program headerPlan plan) rfl t₁ head [] (by simpa using hhead₁) (ambient, ()) none
  have hreverse₂ : t₂ .reverseIndex = encodeWord reverse := by simp [t₂, t₁, hreverse]
  let run₃ := MachineLookup.discardInTime Tape.reverseIndex .clearReverse .nextRow
    (program headerPlan plan) rfl t₂ reverse [] (by simpa using hreverse₂) (ambient, ()) none
  let run₄ : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .nextRow, ((ambient, ()), none), t₃⟩
      (some ⟨some .guard, ((ambient, ()), none), finishTapes base row⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program headerPlan plan .nextRow) _ _) = _
      simp only [program, TM2.stepAux]
      congr 2
      simp [t₃, t₂, t₁, finishTapes, hrow, encodeWord, List.replicate_succ]
    steps_le_m := Nat.le_refl _ }
  let r₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let r₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂ run₃
  have run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃ run₄
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using run

open FinalCNFTableAdapter

@[simp] theorem headRoles_zero : headRoles 0 = Tape.archive := rfl
@[simp] theorem headRoles_one : headRoles 1 = Tape.reverseIndex := rfl
@[simp] theorem headRoles_two : headRoles 2 = Tape.scanWork := rfl
@[simp] theorem headRoles_three : headRoles 3 = Tape.indexWork := rfl
@[simp] theorem headRoles_four : headRoles 4 = Tape.head := rfl
@[simp] theorem headRoles_five : headRoles 5 = Tape.scratch := rfl

def rowOperands (table : GraphTables.Table) (e : Fin table.darts) : Fin 5 → Nat :=
  values table.vertices table.darts table.rows[e].tail.val
    table.rows[table.rows[e].reverseIndex].tail.val e.val

def rowRelation (table : GraphTables.Table) (e : Fin table.darts) : Ambient :=
  ((), fun i => table.rows[e].relation[i])

def rowRest (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) : List Bool :=
  encodeWords (GraphTables.relationWords table.rows[e].relation) ++ rest

def preparedTapes (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) : Tape → List Bool :=
  Lookup.headLookupTapes headRoles
    (endpointTapes base table.rows[e].tail.val table.rows[e].reverseIndex.val
      (rowRest table e rest)) (genericTable table) e

theorem prepared_input (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .input = rowRest table e rest := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

theorem prepared_head (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .head =
      encodeWord table.rows[table.rows[e].reverseIndex].tail.val := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes,
    genericTable_headValue, GraphTables.semantics, ConstraintGraph.head,
    GraphTables.reverseAt]

theorem prepared_tail (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .tail = encodeWord table.rows[e].tail.val ++ base .tail := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

theorem prepared_reverse (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .reverseIndex =
      encodeWord table.rows[e].reverseIndex.val ++ base .reverseIndex := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

theorem prepared_frame (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) (tape : Tape)
    (hi : tape ≠ .input) (ht : tape ≠ .tail) (hr : tape ≠ .reverseIndex)
    (hh : tape ≠ .head) (hs : tape ≠ .scanWork) (hx : tape ≠ .indexWork) :
    preparedTapes base table e rest tape = base tape := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes, hi, ht, hr, hh, hs, hx]

def emittedTapes (plan : Plan) (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) : Tape → List Bool :=
  Function.update (Function.update (preparedTapes base table e rest) Tape.input rest)
    Tape.accumulator ((plan.flatMap (Emitter.commandBits (rowOperands table e)
      (rowRelation table e))).reverse ++ base .accumulator)

def rowResultTapes (plan : Plan) (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) : Tape → List Bool :=
  finishTapes (emittedTapes plan base table e rest) e.val

@[simp] theorem rowResult_input (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .input = rest := by
  simp [rowResultTapes, finishTapes, emittedTapes]

@[simp] theorem rowResult_tail (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .tail = [] := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_head (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .head = [] := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_reverse (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .reverseIndex = [] := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_index (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .rowIndex = encodeWord (e.val + 1) := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_accumulator (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .accumulator =
      (plan.flatMap (Emitter.commandBits (rowOperands table e) (rowRelation table e))).reverse ++
        base .accumulator := by
  simp [rowResultTapes, finishTapes, emittedTapes]

theorem rowResult_frame (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) (tape : Tape)
    (hi : tape ≠ .input) (ht : tape ≠ .tail) (hr : tape ≠ .reverseIndex)
    (hh : tape ≠ .head) (hs : tape ≠ .scanWork) (hx : tape ≠ .indexWork)
    (ha : tape ≠ .accumulator) (hc : tape ≠ .rowIndex) :
    rowResultTapes plan base table e rest tape = base tape := by
  simp only [rowResultTapes, finishTapes, emittedTapes, Function.update_of_ne hi,
    Function.update_of_ne ht, Function.update_of_ne hr, Function.update_of_ne hh,
    Function.update_of_ne ha, Function.update_of_ne hc]
  exact prepared_frame base table e rest tape hi ht hr hh hs hx

def guardRowInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (ambient : Ambient) (hinput : base .input ≠ []) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .guard, ((ambient, ()), none), base⟩
      (some ⟨some .startTail, ((ambient, ()), none), base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .guard) _ _) = _
    cases hb : base .input with
    | nil => exact False.elim (hinput hb)
    | cons b bs => simp [program, guard, TM2.stepAux, hb]
  steps_le_m := Nat.le_refl _

def guardEndInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (ambient : Ambient) (hinput : base .input = []) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .guard, ((ambient, ()), none), base⟩
      (some ⟨some .reverseOutput, ((ambient, ()), none), base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .guard) _ _) = _
    simp [program, guard, TM2.stepAux, hinput]
  steps_le_m := Nat.le_refl _

/-- All five unbounded operands remain isolated encoded naturals after the
row parser and head lookup, including both independently retrieved endpoints. -/
theorem prepared_operands (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool)
    (hn : base .vertices = encodeWord table.vertices)
    (hm : base .darts = encodeWord table.darts)
    (hr : base .rowIndex = encodeWord e.val)
    (ht : base .tail = []) :
    ∀ i, (Function.update (preparedTapes base table e rest) Tape.input rest) (source i) =
      encodeWord (rowOperands table e i) := by
  intro i
  fin_cases i
  · simpa [source, rowOperands, values] using
      prepared_frame base table e rest .vertices (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) |>.trans hn
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.darts = _
    simp only [Function.update_of_ne (show Tape.darts ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .darts (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hm
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.tail = _
    simp only [Function.update_of_ne (show Tape.tail ≠ Tape.input by decide), prepared_tail,
      ht, List.append_nil]
    rfl
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.head = _
    simp only [Function.update_of_ne (show Tape.head ≠ Tape.input by decide), prepared_head]
    rfl
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.rowIndex = _
    simp only [Function.update_of_ne (show Tape.rowIndex ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .rowIndex (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hr

theorem rowOperands_bounded (table : GraphTables.Table) (e : Fin table.darts) :
    ∀ i, rowOperands table e i ≤ (GraphTables.tableBits table).length := by
  intro i
  fin_cases i
  · exact GraphTables.vertices_le_tableBits_length table
  · exact GraphTables.darts_le_tableBits_length table
  · exact table.rows[e].tail.isLt.le.trans (GraphTables.vertices_le_tableBits_length table)
  · exact table.rows[table.rows[e].reverseIndex].tail.isLt.le.trans
      (GraphTables.vertices_le_tableBits_length table)
  · exact e.isLt.le.trans (GraphTables.darts_le_tableBits_length table)

def rowTime (plan : Plan) (N : Nat) : Nat :=
  plan.length * (3 * (N + 1) + 3) + 12 * N + 15

/-- Run one complete stored row, including the actual table-based head lookup.
The only hypotheses describe the physical input tapes; no execution or
serialization correctness of a caller-provided body is assumed. -/
noncomputable def rowInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool)
    (hinput : base .input = encodeWords (GraphTables.rowWords table.rows[e]) ++ rest)
    (harchive : base .archive = GraphTables.tableBits table)
    (hn : base .vertices = encodeWord table.vertices)
    (hm : base .darts = encodeWord table.darts)
    (hrow : base .rowIndex = encodeWord e.val)
    (ht : base .tail = []) (hh : base .head = []) (hr : base .reverseIndex = [])
    (hscratch : base .scratch = []) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .startTail, ((ambient, ()), none), base⟩
      (some ⟨some .guard, ((rowRelation table e, ()), none),
        rowResultTapes plan base table e rest⟩)
      (rowTime plan (GraphTables.tableBits table).length) := by
  let parsed := endpointTapes base table.rows[e].tail.val table.rows[e].reverseIndex.val
    (rowRest table e rest)
  let ready := preparedTapes base table e rest
  let read := Function.update ready Tape.input rest
  let output := emittedTapes plan base table e rest
  let run₁ := endpointsInTime headerPlan plan base table.rows[e].tail.val
    table.rows[e].reverseIndex.val (rowRest table e rest)
    (by simpa [GraphTables.rowWords, encodeWords, List.append_assoc, rowRest] using hinput) ambient
  have parsed_archive : parsed .archive = GenericGraphTables.tableBits (genericTable table) := by
    simpa [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes] using harchive
  have parsed_reverse : parsed .reverseIndex =
      encodeWord (Lookup.headIndex (genericTable table) e).val := by
    simp [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes, hr]
  have parsed_head : parsed .head = [] := by
    simp [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes, hh]
  have parsed_scratch : parsed .scratch = [] := by
    simp [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes, hscratch]
  let run₂ := headPhaseInTime headerPlan plan parsed (genericTable table) e
    parsed_archive parsed_reverse parsed_head parsed_scratch ambient
  let run₃ := relationInTime headerPlan plan ready table.rows[e].relation rest
    (prepared_input base table e rest) ambient
  have read_operands : ∀ i, read (source i) = encodeWord (rowOperands table e i) :=
    prepared_operands base table e rest hn hm hrow ht
  have read_scratch : read .scratch = [] := by
    simp only [read, Function.update_of_ne (show Tape.scratch ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .scratch (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hscratch
  have read_acc : read .accumulator = base .accumulator := by
    simp only [read, Function.update_of_ne (show Tape.accumulator ≠ Tape.input by decide)]
    exact prepared_frame base table e rest .accumulator (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have run₄ : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((rowRelation table e, ()), none), read⟩
      (some ⟨some .clearTail, ((rowRelation table e, ()), none), output⟩)
      (plan.length * (3 * ((GraphTables.tableBits table).length + 1) + 3) + 1) := by
    simpa only [read_acc, output, emittedTapes, read, ready] using
      emitInTime headerPlan plan read (rowOperands table e) read_operands read_scratch
        (rowRelation table e) (GraphTables.tableBits table).length (rowOperands_bounded table e)
  have output_tail : output .tail = encodeWord table.rows[e].tail.val := by
    simp [output, emittedTapes, prepared_tail, ht]
  have output_head : output .head = encodeWord table.rows[table.rows[e].reverseIndex].tail.val := by
    simp [output, emittedTapes, prepared_head]
  have output_reverse : output .reverseIndex = encodeWord table.rows[e].reverseIndex.val := by
    simp [output, emittedTapes, prepared_reverse, hr]
  have output_row : output .rowIndex = encodeWord e.val := by
    simp only [output, emittedTapes,
      Function.update_of_ne (show Tape.rowIndex ≠ Tape.accumulator by decide),
      Function.update_of_ne (show Tape.rowIndex ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .rowIndex (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hrow
  let run₅ := finishInTime headerPlan plan output table.rows[e].tail.val
    table.rows[table.rows[e].reverseIndex].tail.val table.rows[e].reverseIndex.val e.val
    output_tail output_head output_reverse output_row (rowRelation table e)
  let r₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let r₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂ run₃
  let r₁₂₃₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃ run₄
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃₄ run₅
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have hb := run.steps_le_m
  have htbound := rowOperands_bounded table e 2
  have hhbound := rowOperands_bounded table e 3
  have hrbound := table.rows[e].reverseIndex.isLt.le.trans (GraphTables.darts_le_tableBits_length table)
  change table.rows[e].tail.val ≤ _ at htbound
  change table.rows[table.rows[e].reverseIndex].tail.val ≤ _ at hhbound
  simp only [Lookup.headTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, genericTable_tableBits] at hb
  unfold rowTime
  omega

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
