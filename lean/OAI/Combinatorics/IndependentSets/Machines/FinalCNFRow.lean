import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.FinalCNFRowTrace
import OAI.Combinatorics.IndependentSets.PCP.FinalCNFTableAdapter

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

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

end IndependentSetsGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
