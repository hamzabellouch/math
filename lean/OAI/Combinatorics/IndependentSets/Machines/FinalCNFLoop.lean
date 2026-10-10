import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.FinalCNFStream

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.FinalCNFMachine.Program

section

open Turing PCP PCP.AlphabetTable

structure LoopInvariant (table : GraphTables.Table) (r : Nat) (base : Tape → List Bool) : Prop where
  input : base .input = inputStream table (remainingEvents table r)
  archive : base .archive = GraphTables.tableBits table
  vertices : base .vertices = encodeWord table.vertices
  darts : base .darts = encodeWord table.darts
  index : base .rowIndex = encodeWord r
  tail : base .tail = []
  head : base .head = []
  reverse : base .reverseIndex = []
  scratch : base .scratch = []

structure LoopRun (headerPlan plan : Plan) (table : GraphTables.Table) (r remaining : Nat)
    (base : Tape → List Bool) (ambient : Ambient) where
  finalAmbient : Ambient
  finalTapes : Tape → List Bool
  execution : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
    ⟨some .guard, ((ambient, ()), none), base⟩
    (some ⟨some .reverseOutput, ((finalAmbient, ()), none), finalTapes⟩)
    (remaining * (rowTime plan (GraphTables.tableBits table).length + 1) + 1)
  accumulator : finalTapes .accumulator =
    (outputStream plan table (remainingEvents table r)).reverse ++ base .accumulator
  output : finalTapes .output = base .output

theorem rowInvariant_succ (plan : Plan) (table : GraphTables.Table) (r : Nat)
    (hr : r < table.darts) (base : Tape → List Bool) (invariant : LoopInvariant table r base) :
    LoopInvariant table (r + 1)
      (rowResultTapes plan base table ⟨r, hr⟩
        (inputStream table (remainingEvents table (r + 1)))) := by
  constructor
  · exact rowResult_input _ _ _ _ _
  · exact (rowResult_frame _ _ _ _ _ .archive (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.archive
  · exact (rowResult_frame _ _ _ _ _ .vertices (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.vertices
  · exact (rowResult_frame _ _ _ _ _ .darts (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.darts
  · exact rowResult_index _ _ _ _ _
  · exact rowResult_tail _ _ _ _ _
  · exact rowResult_head _ _ _ _ _
  · exact rowResult_reverse _ _ _ _ _
  · exact (rowResult_frame _ _ _ _ _ .scratch (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.scratch

theorem rowWords_nonempty (table : GraphTables.Table) (e : Fin table.darts) :
    encodeWords (GraphTables.rowWords table.rows[e]) ≠ [] := by
  simp [GraphTables.rowWords, encodeWords, encodeWord]

noncomputable def loopInTime (headerPlan plan : Plan) (table : GraphTables.Table)
    (remaining : Nat) :
    ∀ (r : Nat), r + remaining = table.darts → ∀ (base : Tape → List Bool)
      (ambient : Ambient), LoopInvariant table r base →
        LoopRun headerPlan plan table r remaining base ambient := by
  induction remaining with
  | zero =>
      intro r hcount base ambient invariant
      have hr : r = table.darts := by omega
      have hinput : base .input = [] := by
        simpa only [hr, remainingEvents_done, inputStream_nil] using invariant.input
      refine {
        finalAmbient := ambient
        finalTapes := base
        execution := ?_
        accumulator := ?_
        output := rfl }
      · simpa only [Nat.zero_mul, Nat.zero_add] using
          guardEndInTime headerPlan plan base ambient hinput
      · simp only [hr, remainingEvents_done, outputStream_nil, List.reverse_nil, List.nil_append]
  | succ remaining ih =>
      intro r hcount base ambient invariant
      have hr : r < table.darts := by omega
      let e : Fin table.darts := ⟨r, hr⟩
      let rest := inputStream table (remainingEvents table (r + 1))
      let next := rowResultTapes plan base table e rest
      have hinput : base .input = encodeWords (GraphTables.rowWords table.rows[e]) ++ rest := by
        rw [invariant.input, inputStream_remaining_cons table r hr]
      have hnonempty : base .input ≠ [] := by
        rw [hinput]
        exact List.append_ne_nil_of_left_ne_nil (rowWords_nonempty table e) rest
      let guardRun := guardRowInTime headerPlan plan base ambient hnonempty
      let rowRun := rowInTime headerPlan plan base table e rest hinput invariant.archive
        invariant.vertices invariant.darts invariant.index invariant.tail invariant.head
        invariant.reverse invariant.scratch ambient
      let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guardRun rowRun
      let later := ih (r + 1) (by omega) next (rowRelation table e)
        (rowInvariant_succ plan table r hr base invariant)
      let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first later.execution
      refine {
        finalAmbient := later.finalAmbient
        finalTapes := later.finalTapes
        execution := { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
        accumulator := ?_
        output := ?_ }
      · have hb := run.steps_le_m
        rw [Nat.succ_mul]
        omega
      · rw [later.accumulator, outputStream_remaining_cons plan table r hr]
        simp only [next, rowResult_accumulator, List.reverse_append, List.append_assoc]
        rfl
      · rw [later.output]
        exact rowResult_frame _ _ _ _ _ .output (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)

end

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

def emittedBytes (plan : Plan) (table : GraphTables.Table) : List Bool :=
  encodeWords [6 * table.vertices + 36864 * table.darts, 40960 * table.darts] ++
    outputStream plan table (List.finRange table.darts)

noncomputable def rawBudget (plan : Plan) (table : GraphTables.Table) : Nat :=
  headerTimePolynomial.eval (GraphTables.tableBits table).length +
    table.darts * (rowTime plan (GraphTables.tableBits table).length + 1) + 1 +
      (emittedBytes plan table).length + 1

structure RawRun (plan : Plan) (table : GraphTables.Table) where
  finalAmbient : Ambient
  finalTapes : Tape → List Bool
  execution : StateTransition.EvalsToInTime (machine headerPlan plan).step
    (initList (machine headerPlan plan) (GraphTables.tableBits table))
    (some ⟨none, ((finalAmbient, ()), none), finalTapes⟩) (rawBudget plan table)
  output : finalTapes .output = emittedBytes plan table

theorem header_loopInvariant (_ : Plan) (table : GraphTables.Table) :
    LoopInvariant table 0 (headerResultTapes table.vertices table.darts
      (tableRowsBits (genericTable table))) := by
  constructor
  · rw [headerResultTapes_input, inputStream_remaining_zero]
  · rw [headerResultTapes_archive]
    exact (tableBits_header_rows (genericTable table)).symm.trans (genericTable_tableBits table)
  · rfl
  · rfl
  · exact headerResultTapes_rowIndex _ _ _
  · rfl
  · rfl
  · rfl
  · rfl

noncomputable def rawRun (plan : Plan) (table : GraphTables.Table) : RawRun plan table := by
  let base := headerResultTapes table.vertices table.darts (tableRowsBits (genericTable table))
  let ambient : Ambient := ((), fun _ => false)
  have headerRun : StateTransition.EvalsToInTime (machine headerPlan plan).step
      (initList (machine headerPlan plan) (GraphTables.tableBits table))
      (some ⟨some .guard, ((ambient, ()), none), base⟩)
      (headerTimePolynomial.eval (GraphTables.tableBits table).length) := by
    simpa only [genericTable_tableBits, genericTable_vertices, genericTable_darts, base, ambient]
      using initializedTableHeaderInTime plan (genericTable table)
  let loop := loopInTime headerPlan plan table table.darts 0 (by omega)
    base ambient (header_loopInvariant plan table)
  have acc : loop.finalTapes .accumulator = (emittedBytes plan table).reverse := by
    rw [loop.accumulator]
    simp only [remainingEvents_zero, base, headerResultTapes_accumulator, emittedBytes,
      List.reverse_append]
  have out : loop.finalTapes .output = [] := by
    rw [loop.output]
    rfl
  let finalTapes := Reduction.MachineTransfer.tapesAt Tape.accumulator Tape.output
    loop.finalTapes [] (emittedBytes plan table)
  have finish : StateTransition.EvalsToInTime (machine headerPlan plan).step
      ⟨some .reverseOutput, ((loop.finalAmbient, ()), none), loop.finalTapes⟩
      (some ⟨none, ((loop.finalAmbient, ()), none), finalTapes⟩)
      ((emittedBytes plan table).length + 1) := by
    have run := Reduction.MachineTransfer.transferAtInTime Tape.accumulator Tape.output
      (by decide) id false .reverseOutput none (program headerPlan plan) rfl
      loop.finalTapes (loop.finalAmbient, ()) none
    simp only [acc, out, List.reverse_reverse, List.length_reverse, List.map_id,
      List.append_nil] at run
    exact run
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ headerRun loop.execution
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first finish
  exact {
    finalAmbient := loop.finalAmbient
    finalTapes := finalTapes
    execution := {
      toEvalsTo := run.toEvalsTo
      steps_le_m := by
        have hb := run.steps_le_m
        unfold rawBudget
        omega }
    output := by simp [finalTapes, Reduction.MachineTransfer.tapesAt] }

end IndependentSetsGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
