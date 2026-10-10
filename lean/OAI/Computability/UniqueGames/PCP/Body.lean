import OAI.Computability.UniqueGames.PCP.DriverLemmas
import OAI.Computability.UniqueGames.PCP.LoopState

namespace OAI

/-!
One actual iteration of the alphabet-table driver. The positive unary guard,
row parser, preserving head lookup, comparison, finite emission plan, three
drains, and unary index increment all execute inside `Driver.program`.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Body

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def bodyTime (q N : Nat) : Nat :=
  (32 + 8 * (Enumeration.localCount q * (6 * (2 * 4104)))) * (N + 1)

/-- An execution witness, with the exact invariant needed by the next guard. -/
structure RowStepResult (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) (oldRelation : GenericGraphTables.RelationTable q)
    (oldFlag : Bool) where
  tapes : Tape → List Bool
  ready : LoopState.Ready input (e.val + 1) tapes
  run : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    ⟨some .guard, normal oldRelation oldFlag, base⟩
    (some ⟨some .guard, CompareLoop.rowState input e, tapes⟩)
    (bodyTime q (LoopState.inputBits input).length)

def guardTapes (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) : Tape → List Bool :=
  Function.update base .counter (encodeWord (input.darts - (e.val + 1)))

def parsedTapes (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) : Tape → List Bool :=
  Lookup.readRowTapes .cursor .tail .reverseIndex (guardTapes input e base)
    input.rows[e] (LoopState.cursorBits input (e.val + 1))

def workingTapes (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) : Tape → List Bool :=
  Lookup.headLookupTapes headPorts (parsedTapes input e base) input e

def emittedTapes (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) : Tape → List Bool :=
  Emitter.resultTapes .reversed (workingTapes input e base)
    (encodeWords (EmitRows.blockWords input e))

def clearFieldsTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update base .tail []) .reverseIndex []) .head []

/-- Exact final tapes, including the lookup's retained scan suffixes. -/
def resultTapes (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (clearFieldsTapes (emittedTapes input e base)) .edge
    (encodeWord (e.val + 1))

private theorem workingTapes_other (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) (other : Tape)
    (hcounter : other ≠ .counter) (hcursor : other ≠ .cursor)
    (htail : other ≠ .tail) (hreverse : other ≠ .reverseIndex)
    (hscan : other ≠ .scan) (hindex : other ≠ .indexScan) (hhead : other ≠ .head) :
    workingTapes input e base other = base other := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes, guardTapes, hcounter, hcursor, htail,
    hreverse, hscan, hindex, hhead]

private theorem workingTapes_counter (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) :
    workingTapes input e base .counter = encodeWord (input.darts - (e.val + 1)) := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes, guardTapes]

private theorem workingTapes_cursor (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) :
    workingTapes input e base .cursor = LoopState.cursorBits input (e.val + 1) := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes]

private theorem workingTapes_tail (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) :
    workingTapes input e base .tail = encodeWord input.rows[e].tail.val := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes]

private theorem workingTapes_reverse (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) :
    workingTapes input e base .reverseIndex = encodeWord input.rows[e].reverseIndex.val := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes]

private theorem workingTapes_head (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) :
    workingTapes input e base .head =
      encodeWord input.rows[input.rows[e].reverseIndex].tail.val := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    Lookup.headValue, Lookup.headIndex]

/-- The three cleanup phases are actual drains in the concrete program. -/
def clearFieldsInTime (base : Tape → List Bool) (ambient : Ambient q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some (.clearField 0), (ambient, none), base⟩
      (some ⟨some .increment, (ambient, none), clearFieldsTapes base⟩)
      ((base .tail).length + (base .reverseIndex).length + (base .head).length + 3) := by
  let first := MachineDrain.drainInTime Tape.tail (Driver.Label.clearField 0)
    (some (.clearField 1)) (Driver.program q) (by rfl) base ambient none
  let second := MachineDrain.drainInTime Tape.reverseIndex (Driver.Label.clearField 1)
    (some (.clearField 2)) (Driver.program q) (by rfl)
    (Function.update base .tail []) ambient none
  let third := MachineDrain.drainInTime Tape.head (Driver.Label.clearField 2)
    (some .increment) (Driver.program q) (by rfl)
    (Function.update (Function.update base .tail []) .reverseIndex []) ambient none
  let firstTwo := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstTwo third
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have h := run.steps_le_m
  simp only [Function.update_of_ne (by decide : Tape.reverseIndex ≠ .tail),
    Function.update_of_ne (by decide : Tape.head ≠ .reverseIndex),
    Function.update_of_ne (by decide : Tape.head ≠ .tail)] at h
  omega

def incrementInTime (base : Tape → List Bool) (ambient : Ambient q)
    (e : Nat) (he : base .edge = encodeWord e) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .increment, (ambient, none), base⟩
      (some ⟨some .guard, (ambient, none), Function.update base .edge (encodeWord (e + 1))⟩)
      1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (nextRow (Driver.Label.guard : Driver.Label q))
      (ambient, none) base) = _
    simpa only [List.append_nil] using congrArg some
      (stepAux_nextRow (Driver.Label.guard : Driver.Label q) (ambient, none) base e []
        (by simpa only [List.append_nil] using he))
  steps_le_m := Nat.le_refl _

private theorem emitterView_at (label :
    Emitter.Label (Driver.rowPlan q).length (Addresses.fieldBound q)) :
    (MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
      (Driver.program q)) (.emit label) =
      Emitter.statement (Emitter.listCommands (Driver.rowPlan q)) rowSources
        Tape.scratch Tape.reversed Driver.Label.emit (some (.clearField 0)) label := by
  change MachineControl.statement id (emitterEquiv q).symm
    (MachineControl.statement id (emitterEquiv q) _) = _
  exact MachineFieldProfile.statement_roundtrip (emitterEquiv q).symm _

private theorem context_rowState (input : GenericGraphTables.Table q)
    (e : Fin input.darts) :
    context (CompareLoop.rowState input e).1 = EmitRows.rowContext input e := by
  change (input.rows[e].relation,
    decide (input.rows[e].tail.val = input.rows[input.rows[e].reverseIndex].tail.val)) =
      (input.rows[e].relation,
        decide (input.rows[e].tail = input.rows[input.rows[e].reverseIndex].tail))
  simp only [Fin.val_inj]

/-- Execute the actual emitted row block through the finite register equivalence. -/
def emitInTime (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool)
    (operands : ∀ i, base (rowSources i) = encodeWord (EmitRows.rowValues input e i))
    (scratchEmpty : base .scratch = []) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some (Driver.rowEntry q), CompareLoop.rowState input e, base⟩
      (some ⟨some (.clearField 0), CompareLoop.rowState input e,
        Emitter.resultTapes .reversed base (encodeWords (EmitRows.blockWords input e))⟩)
      (Enumeration.localCount q * (6 * (2 * 4104)) *
        (3 * ((LoopState.inputBits input).length + 1) + 3) + 1) := by
  let view := MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
    (Driver.program q)
  have sourceScratch : ∀ i : Fin 5, rowSources i ≠ Tape.scratch := by
    intro i; fin_cases i <;> decide
  have sourceOutput : ∀ i : Fin 5, rowSources i ≠ Tape.reversed := by
    intro i; fin_cases i <;> decide
  have bounded : ∀ i, EmitRows.rowValues input e i ≤ (LoopState.inputBits input).length := by
    have hn := GenericGraphTables.vertices_le_tableBits_length input
    have hm := GenericGraphTables.darts_le_tableBits_length input
    have he := e.isLt
    have ht := input.rows[e].tail.isLt
    have hh := input.rows[input.rows[e].reverseIndex].tail.isLt
    intro i
    fin_cases i <;> simp [EmitRows.rowValues, Addresses.values, LoopState.inputBits] <;> omega
  have run := EmitRows.blockInTimeAmbient input e (@context q)
    (CompareLoop.rowState input e).1 (context_rowState input e)
    rowSources Tape.scratch Tape.reversed sourceScratch sourceOutput (by decide)
    Driver.Label.emit (some (.clearField 0)) view emitterView_at base operands
    scratchEmpty (LoopState.inputBits input).length bounded
  have restored : MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q) view =
      Driver.program q := by
    funext label
    exact MachineFieldProfile.statement_roundtrip (emitterEquiv q) (Driver.program q label)
  have transported := transportInTime (emitterEquiv q) view run
  rw [restored] at transported
  simpa [MachineControl.configuration, emitterEquiv, Option.map_some, id_eq,
    Driver.rowEntry, Driver.rowPlan, CompareLoop.rowState, normal] using transported

private theorem result_ready (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) (ready : LoopState.Ready input e.val base) :
    LoopState.Ready input (e.val + 1) (resultTapes input e base) := by
  constructor
  · exact Nat.succ_le_of_lt e.isLt
  all_goals simp [resultTapes, clearFieldsTapes, emittedTapes, Emitter.resultTapes,
    workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes, guardTapes, ready.original, ready.vertices,
    ready.darts, ready.scratch, ready.compareLeft, ready.compareRight, ready.output,
    ready.reversed, LoopState.prefixBits_reverse_succ input e.val e.isLt]

private theorem workingOperands (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) (ready : LoopState.Ready input e.val base) :
    ∀ i, workingTapes input e base (rowSources i) =
      encodeWord (EmitRows.rowValues input e i) := by
  intro i
  fin_cases i <;> simp [rowSources, EmitRows.rowValues, Addresses.values,
    workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes, guardTapes, Lookup.headValue, Lookup.headIndex,
    ready.vertices, ready.darts, ready.edge]

/-- Execute a whole row iteration from the exact guard invariant. Every run
below is obtained from the concrete code at its component labels. -/
def rowStep (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) (ready : LoopState.Ready input e.val base)
    (oldRelation : GenericGraphTables.RelationTable q) (oldFlag : Bool) :
    RowStepResult input e base oldRelation oldFlag := by
  let N := (LoopState.inputBits input).length
  have guarded : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .guard, normal oldRelation oldFlag, base⟩
      (some ⟨some .tailStart, normal oldRelation oldFlag, guardTapes input e base⟩) 1 := by
    have hbase : MachineUnaryCounter.counterTapes .counter base
        (input.darts - (e.val + 1) + 1) [] = base := by
      simp only [MachineUnaryCounter.counterTapes, List.append_nil,
        ← ready.counter_succ e.isLt, Function.update_eq_self]
    have run := MachineUnaryCounter.guardInTime_succ Tape.counter Driver.Label.guard
      .tailStart .reverseOutput (Driver.program q) (by rfl) base
      (input.darts - (e.val + 1)) [] (normal oldRelation oldFlag).1 none
    rw [hbase] at run
    simpa only [MachineUnaryCounter.counterTapes, List.append_nil, guardTapes,
      normal] using run
  have parsed : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .tailStart, normal oldRelation oldFlag, guardTapes input e base⟩
      (some ⟨some .headCopyFirst, normal input.rows[e].relation oldFlag,
        parsedTapes input e base⟩) (Lookup.readRowCost input.rows[e]) := by
    have hcursor : guardTapes input e base .cursor = Lookup.rowBits input.rows[e] ++
        LoopState.cursorBits input (e.val + 1) := by
      simpa only [guardTapes, Function.update_of_ne (by decide : Tape.cursor ≠ .counter),
        Lookup.rowBits] using ready.cursor.trans (LoopState.cursorBits_succ input e.val e.isLt)
    have htail : guardTapes input e base .tail = [] := by simp [guardTapes, ready.tail]
    have hreverse : guardTapes input e base .reverseIndex = [] := by
      simp [guardTapes, ready.reverseIndex]
    simpa only [normal, parsedTapes] using
      Lookup.readRowInTime Tape.cursor Tape.tail Tape.reverseIndex
        (by decide) (by decide) (by decide) Driver.Label.tailStart .tailLoop
        .reverseStart .reverseLoop .readPredicate .headCopyFirst (Driver.program q)
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (guardTapes input e base) input.rows[e] (LoopState.cursorBits input (e.val + 1))
        hcursor htail hreverse (oldFlag, false, none) oldRelation none
  have looked : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .headCopyFirst, normal input.rows[e].relation oldFlag, parsedTapes input e base⟩
      (some ⟨some (.compare .leftFirst), normal input.rows[e].relation oldFlag,
        workingTapes input e base⟩) (7 * N + 5) := by
    have htable : parsedTapes input e base (headPorts 0) = GenericGraphTables.tableBits input := by
      simpa [headPorts, parsedTapes, Lookup.readRowTapes, guardTapes,
        LoopState.inputBits] using ready.original
    have hreverse : parsedTapes input e base (headPorts 1) =
        encodeWord (Lookup.headIndex input e).val := by
      simp [headPorts, parsedTapes, Lookup.readRowTapes, Lookup.headIndex]
    have hhead : parsedTapes input e base (headPorts 4) = [] := by
      simp [headPorts, parsedTapes, Lookup.readRowTapes, guardTapes, ready.head]
    have hscratch : parsedTapes input e base (headPorts 5) = [] := by
      simp [headPorts, parsedTapes, Lookup.readRowTapes, guardTapes, ready.scratch]
    have run := Lookup.headLookupInTime headPorts headPorts_injective
      Driver.Label.headCopyFirst .headCopySecond .indexCopyFirst .indexCopySecond
      .headVertices .headDarts Driver.Label.headLookup (some (.compare .leftFirst))
      (Driver.program q) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (fun _ => rfl) (parsedTapes input e base) input e htable hreverse hhead hscratch
      (normal input.rows[e].relation oldFlag).1 none
    simpa only [workingTapes, normal, N, LoopState.inputBits, Lookup.headTimePolynomial,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using run
  have hleft : workingTapes input e base .compareLeft = [] :=
    (workingTapes_other input e base .compareLeft (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans ready.compareLeft
  have hright : workingTapes input e base .compareRight = [] :=
    (workingTapes_other input e base .compareRight (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans ready.compareRight
  have hscratch : workingTapes input e base .scratch = [] :=
    (workingTapes_other input e base .scratch (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans ready.scratch
  let compared := CompareLoop.compareRowInTime Driver.Label.compare (Driver.rowEntry q)
    (Driver.program q) (fun _ => rfl) input e (workingTapes input e base)
    (workingTapes_tail input e base) (workingTapes_head input e base)
    hleft hright hscratch oldFlag
  let emitted := emitInTime input e (workingTapes input e base)
    (workingOperands input e base ready) hscratch
  let cleared := clearFieldsInTime (emittedTapes input e base) (CompareLoop.rowState input e).1
  have hedge : clearFieldsTapes (emittedTapes input e base) .edge = encodeWord e.val := by
    simp [clearFieldsTapes, emittedTapes, Emitter.resultTapes, workingTapes,
      Lookup.headLookupTapes, MachineLookup.tapes, headPorts, parsedTapes,
      Lookup.readRowTapes, guardTapes, ready.edge]
  let incremented := incrementInTime (clearFieldsTapes (emittedTapes input e base))
    (CompareLoop.rowState input e).1 e.val hedge
  let run₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guarded parsed
  let run₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ looked
  let run₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₂ compared
  let run₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₃ emitted
  let run₅ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₄ cleared
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₅ incremented
  refine {
    tapes := resultTapes input e base
    ready := result_ready input e base ready
    run := { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  }
  have hn : input.vertices ≤ N := GenericGraphTables.vertices_le_tableBits_length input
  have hm : input.darts ≤ N := GenericGraphTables.darts_le_tableBits_length input
  have hr : Lookup.readRowCost input.rows[e] ≤ 2 * N + 5 :=
    Lookup.readRowCost_table_le input e
  have ht : (emittedTapes input e base .tail).length ≤ N := by
    simp only [emittedTapes, Emitter.resultTapes,
      Function.update_of_ne (by decide : Tape.tail ≠ .reversed), workingTapes_tail,
      encodeWord_length]
    exact (Nat.succ_le_of_lt input.rows[e].tail.isLt).trans hn
  have hv : (emittedTapes input e base .reverseIndex).length ≤ N := by
    simp only [emittedTapes, Emitter.resultTapes,
      Function.update_of_ne (by decide : Tape.reverseIndex ≠ .reversed), workingTapes_reverse,
      encodeWord_length]
    exact (Nat.succ_le_of_lt input.rows[e].reverseIndex.isLt).trans hm
  have hh : (emittedTapes input e base .head).length ≤ N := by
    simp only [emittedTapes, Emitter.resultTapes,
      Function.update_of_ne (by decide : Tape.head ≠ .reversed), workingTapes_head,
      encodeWord_length]
    exact (Nat.succ_le_of_lt input.rows[input.rows[e].reverseIndex].tail.isLt).trans hn
  have budget := run.steps_le_m
  change run.steps ≤ (32 + 8 * (Enumeration.localCount q * (6 * (2 * 4104)))) * (N + 1)
  nlinarith

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Body

end OAI
