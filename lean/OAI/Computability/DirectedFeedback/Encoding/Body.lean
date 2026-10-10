import Mathlib
import OAI.Computability.DirectedFeedback.Encoding.EmitRows

namespace OAI


namespace DFVSGames.Foundations.PCP.AlphabetTable.Body

open Turing
open DFVSGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def bodyTime (q N : Nat) : Nat :=
  (32 + 8 * (Enumeration.localCount q * (6 * (2 * 4104)))) * (N + 1)

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

def resultTapes (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (clearFieldsTapes (emittedTapes input e base)) .edge
    (encodeWord (e.val + 1))

private theorem workingTapes_other_inline_Body (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) (other : Tape)
    (hcounter : other ≠ .counter) (hcursor : other ≠ .cursor)
    (htail : other ≠ .tail) (hreverse : other ≠ .reverseIndex)
    (hscan : other ≠ .scan) (hindex : other ≠ .indexScan) (hhead : other ≠ .head) :
    workingTapes input e base other = base other := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes, guardTapes, hcounter, hcursor, htail,
    hreverse, hscan, hindex, hhead]

private theorem workingTapes_counter_inline_Body (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) :
    workingTapes input e base .counter = encodeWord (input.darts - (e.val + 1)) := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes, guardTapes]

private theorem workingTapes_cursor_inline_Body (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) :
    workingTapes input e base .cursor = LoopState.cursorBits input (e.val + 1) := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes]

private theorem workingTapes_tail_inline_Body (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) :
    workingTapes input e base .tail = encodeWord input.rows[e].tail.val := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes]

private theorem workingTapes_reverse_inline_Body (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) :
    workingTapes input e base .reverseIndex = encodeWord input.rows[e].reverseIndex.val := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes]

private theorem workingTapes_head_inline_Body (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) :
    workingTapes input e base .head =
      encodeWord input.rows[input.rows[e].reverseIndex].tail.val := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    Lookup.headValue, Lookup.headIndex]

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

private theorem emitterView_at_inline_Body (label :
    Emitter.Label (Driver.rowPlan q).length (Addresses.fieldBound q)) :
    (MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
      (Driver.program q)) (.emit label) =
      Emitter.statement (Emitter.listCommands (Driver.rowPlan q)) rowSources
        Tape.scratch Tape.reversed Driver.Label.emit (some (.clearField 0)) label := by
  change MachineControl.statement id (emitterEquiv q).symm
    (MachineControl.statement id (emitterEquiv q) _) = _
  exact MachineFieldProfile.statement_roundtrip (emitterEquiv q).symm _

private theorem context_rowState_inline_Body (input : GenericGraphTables.Table q)
    (e : Fin input.darts) :
    context (CompareLoop.rowState input e).1 = EmitRows.rowContext input e := by
  change (input.rows[e].relation,
    decide (input.rows[e].tail.val = input.rows[input.rows[e].reverseIndex].tail.val)) =
      (input.rows[e].relation,
        decide (input.rows[e].tail = input.rows[input.rows[e].reverseIndex].tail))
  simp only [Fin.val_inj]

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
    (CompareLoop.rowState input e).1 (context_rowState_inline_Body input e)
    rowSources Tape.scratch Tape.reversed sourceScratch sourceOutput (by decide)
    Driver.Label.emit (some (.clearField 0)) view emitterView_at_inline_Body base operands
    scratchEmpty (LoopState.inputBits input).length bounded
  have restored : MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q) view =
      Driver.program q := by
    funext label
    exact MachineFieldProfile.statement_roundtrip (emitterEquiv q) (Driver.program q label)
  have transported := transportInTime (emitterEquiv q) view run
  rw [restored] at transported
  simpa [MachineControl.configuration, emitterEquiv, Option.map_some, id_eq,
    Driver.rowEntry, Driver.rowPlan, CompareLoop.rowState, normal] using transported

private theorem result_ready_inline_Body (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) (ready : LoopState.Ready input e.val base) :
    LoopState.Ready input (e.val + 1) (resultTapes input e base) := by
  constructor
  · exact Nat.succ_le_of_lt e.isLt
  all_goals simp [resultTapes, clearFieldsTapes, emittedTapes, Emitter.resultTapes,
    workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes, guardTapes, ready.original, ready.vertices,
    ready.darts, ready.scratch, ready.compareLeft, ready.compareRight, ready.output,
    ready.reversed, LoopState.prefixBits_reverse_succ input e.val e.isLt]

private theorem workingOperands_inline_Body (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) (ready : LoopState.Ready input e.val base) :
    ∀ i, workingTapes input e base (rowSources i) =
      encodeWord (EmitRows.rowValues input e i) := by
  intro i
  fin_cases i <;> simp [rowSources, EmitRows.rowValues, Addresses.values,
    workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes, guardTapes, Lookup.headValue, Lookup.headIndex,
    ready.vertices, ready.darts, ready.edge]

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
    (workingTapes_other_inline_Body input e base .compareLeft (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans ready.compareLeft
  have hright : workingTapes input e base .compareRight = [] :=
    (workingTapes_other_inline_Body input e base .compareRight (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans ready.compareRight
  have hscratch : workingTapes input e base .scratch = [] :=
    (workingTapes_other_inline_Body input e base .scratch (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans ready.scratch
  let compared := CompareLoop.compareRowInTime Driver.Label.compare (Driver.rowEntry q)
    (Driver.program q) (fun _ => rfl) input e (workingTapes input e base)
    (workingTapes_tail_inline_Body input e base) (workingTapes_head_inline_Body input e base)
    hleft hright hscratch oldFlag
  let emitted := emitInTime input e (workingTapes input e base)
    (workingOperands_inline_Body input e base ready) hscratch
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
    ready := result_ready_inline_Body input e base ready
    run := { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  }
  have hn : input.vertices ≤ N := GenericGraphTables.vertices_le_tableBits_length input
  have hm : input.darts ≤ N := GenericGraphTables.darts_le_tableBits_length input
  have hr : Lookup.readRowCost input.rows[e] ≤ 2 * N + 5 :=
    Lookup.readRowCost_table_le input e
  have ht : (emittedTapes input e base .tail).length ≤ N := by
    simp only [emittedTapes, Emitter.resultTapes,
      Function.update_of_ne (by decide : Tape.tail ≠ .reversed), workingTapes_tail_inline_Body,
      encodeWord_length]
    exact (Nat.succ_le_of_lt input.rows[e].tail.isLt).trans hn
  have hv : (emittedTapes input e base .reverseIndex).length ≤ N := by
    simp only [emittedTapes, Emitter.resultTapes,
      Function.update_of_ne (by decide : Tape.reverseIndex ≠ .reversed), workingTapes_reverse_inline_Body,
      encodeWord_length]
    exact (Nat.succ_le_of_lt input.rows[e].reverseIndex.isLt).trans hm
  have hh : (emittedTapes input e base .head).length ≤ N := by
    simp only [emittedTapes, Emitter.resultTapes,
      Function.update_of_ne (by decide : Tape.head ≠ .reversed), workingTapes_head_inline_Body,
      encodeWord_length]
    exact (Nat.succ_le_of_lt input.rows[input.rows[e].reverseIndex].tail.isLt).trans hn
  have budget := run.steps_le_m
  change run.steps ≤ (32 + 8 * (Enumeration.localCount q * (6 * (2 * 4104)))) * (N + 1)
  nlinarith

end DFVSGames.Foundations.PCP.AlphabetTable.Body


namespace DFVSGames.Foundations.PCP.AlphabetTable.Initialization

open Turing
open DFVSGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def inputTapes (input : GenericGraphTables.Table q) : Tape → List Bool
  | .original => GenericGraphTables.tableBits input
  | _ => []

def rowsBits (input : GenericGraphTables.Table q) : List Bool :=
  encodeWords ((GenericGraphTables.rowList input).flatMap GenericGraphTables.rowWords)

def headerBits (input : GenericGraphTables.Table q) : List Bool :=
  encodeWords [Enumeration.vertexCount input.vertices input.darts q,
    Enumeration.dartCount input.darts q]

def setupTapes (input : GenericGraphTables.Table q) : Tape → List Bool
  | .original => GenericGraphTables.tableBits input
  | .cursor => rowsBits input
  | .vertices => encodeWord input.vertices
  | .darts | .counter => encodeWord input.darts
  | .edge => encodeWord 0
  | _ => []

def loopTapes (input : GenericGraphTables.Table q) : Tape → List Bool
  | .original => GenericGraphTables.tableBits input
  | .cursor => rowsBits input
  | .vertices => encodeWord input.vertices
  | .darts | .counter => encodeWord input.darts
  | .edge => encodeWord 0
  | .reversed => (headerBits input).reverse
  | _ => []

def loopStart (input : GenericGraphTables.Table q) :
    TM2.Cfg Alphabet (Driver.Label q) (State q) :=
  ⟨some .guard, initial q, loopTapes input⟩

theorem setupResult_eq (input : GenericGraphTables.Table q) :
    Setup.resultTapes setupPorts (inputTapes input) input.vertices input.darts (rowsBits input) =
      setupTapes input := by
  funext tape
  cases tape <;> simp [Setup.resultTapes, setupPorts, inputTapes, setupTapes]

theorem headerResult_eq (input : GenericGraphTables.Table q) :
    Emitter.resultTapes Tape.reversed (setupTapes input) (headerBits input) = loopTapes input := by
  funext tape
  cases tape <;> simp [Emitter.resultTapes, setupTapes, loopTapes]

theorem machineInitial_eq (input : GenericGraphTables.Table q) :
    initList (Driver.machine q) (GenericGraphTables.tableBits input) =
      (⟨some (.setup .copyFirst), initial q, inputTapes input⟩ :
        TM2.Cfg Alphabet (Driver.Label q) (State q)) := by
  change (⟨some (.setup .copyFirst), initial q, _⟩ :
    TM2.Cfg Alphabet (Driver.Label q) (State q)) = _
  congr 1
  funext tape
  cases tape <;> rfl

def setupInTime (input : GenericGraphTables.Table q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some ⟨some (Driver.headerEntry q), initial q, setupTapes input⟩)
      (6 * (GenericGraphTables.tableBits input).length + 11) := by
  have initialized : ∀ i : Fin 7, inputTapes input (setupPorts i) =
      if i = 0 then GenericGraphTables.tableBits input else [] := by
    intro i
    fin_cases i <;> rfl
  have run := Setup.tableSetupInTime setupPorts setupPorts_injective Driver.Label.setup
    (some (Driver.headerEntry q)) (Driver.program q) (Driver.program_setup q)
    (inputTapes input) input initialized (initial q).1 none
  have initialState : ((initial q).1, (none : Option Bool)) = initial q := rfl
  have result := setupResult_eq input
  unfold rowsBits at result
  rw [initialState, result] at run
  rw [machineInitial_eq]
  exact run

private theorem headerView_at_inline_Initialization (label : Emitter.Label (Driver.headerPlan q).length
    (Addresses.fieldBound q)) :
    (MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
      (Driver.program q)) (.header label) =
      Emitter.statement (Emitter.listCommands (Driver.headerPlan q)) headerSources
        Tape.scratch Tape.reversed Driver.Label.header (some .guard) label := by
  change MachineControl.statement id (emitterEquiv q).symm
    (MachineControl.statement id (emitterEquiv q) _) = _
  exact MachineFieldProfile.statement_roundtrip (emitterEquiv q).symm _

def headerInTime (input : GenericGraphTables.Table q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some (Driver.headerEntry q), initial q, setupTapes input⟩
      (some (loopStart input))
      (7 * (3 * ((GenericGraphTables.tableBits input).length + 1) + 3) + 1) := by
  let view := MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
    (Driver.program q)
  have sourceScratch : ∀ i : Fin 2, headerSources i ≠ Tape.scratch := by
    intro i
    fin_cases i <;> decide
  have sourceOutput : ∀ i : Fin 2, headerSources i ≠ Tape.reversed := by
    intro i
    fin_cases i <;> decide
  have operands : ∀ i : Fin 2, setupTapes input (headerSources i) =
      encodeWord (![input.vertices, input.darts] i) := by
    intro i
    fin_cases i <;> rfl
  have run := EmitRows.headerInTime q input.vertices input.darts headerSources
    Tape.scratch Tape.reversed sourceScratch sourceOutput (by decide)
    Driver.Label.header (some .guard) view headerView_at_inline_Initialization
    (setupTapes input) operands (by rfl) (initial q).1
    (GenericGraphTables.tableBits input).length
    (GenericGraphTables.vertices_le_tableBits_length input)
    (GenericGraphTables.darts_le_tableBits_length input)
  have restored : MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q) view =
      Driver.program q := by
    funext label
    exact MachineFieldProfile.statement_roundtrip (emitterEquiv q) (Driver.program q label)
  have transported := transportInTime (emitterEquiv q) view run
  rw [restored] at transported
  change StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    ⟨some (Driver.headerEntry q), initial q, setupTapes input⟩
    (some ⟨some .guard, initial q,
      Emitter.resultTapes Tape.reversed (setupTapes input) (headerBits input)⟩)
    (7 * (3 * ((GenericGraphTables.tableBits input).length + 1) + 3) + 1) at transported
  rw [headerResult_eq] at transported
  exact transported

def time (N : Nat) : Nat := (6 * N + 11) + (7 * (3 * (N + 1) + 3) + 1)

theorem time_eq (N : Nat) : time N = 27 * N + 54 := by
  unfold time
  omega

def initializeInTime (input : GenericGraphTables.Table q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some (loopStart input)) (time (GenericGraphTables.tableBits input).length) := by
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (setupInTime input) (headerInTime input)
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have bound := run.steps_le_m
  unfold time
  omega

end DFVSGames.Foundations.PCP.AlphabetTable.Initialization


namespace DFVSGames.Foundations.PCP.AlphabetTable.LoopInitialization

open DFVSGames.Foundations.Complexity
open RuntimeModel LoopState

theorem initialization_ready {q : Nat} (input : GenericGraphTables.Table q) :
    Ready input 0 (Initialization.loopTapes input) where
  le_darts := Nat.zero_le _
  original := rfl
  cursor := by
    change Initialization.rowsBits input = cursorBits input 0
    rw [cursorBits_zero]
    rfl
  vertices := rfl
  darts := rfl
  counter := by simp [Initialization.loopTapes]
  edge := rfl
  tail := rfl
  reverseIndex := rfl
  head := rfl
  scratch := rfl
  compareLeft := rfl
  compareRight := rfl
  output := rfl
  reversed := by
    change (Initialization.headerBits input).reverse = (prefixBits input 0).reverse
    rw [prefixBits_zero]
    rfl

end DFVSGames.Foundations.PCP.AlphabetTable.LoopInitialization


namespace DFVSGames.Foundations.PCP.AlphabetTable.Loop

open Turing
open DFVSGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def zeroGuardInTime (input : GenericGraphTables.Table q) (base : Tape → List Bool)
    (ready : LoopState.Ready input input.darts base)
    (relation : GenericGraphTables.RelationTable q) (flag : Bool) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .guard, normal relation flag, base⟩
      (some ⟨some .reverseOutput, normal relation flag, base⟩) 1 := by
  have counterSelf : MachineUnaryCounter.counterTapes Tape.counter base 0 [] = base := by
    simp only [MachineUnaryCounter.counterTapes, List.append_nil,
      ← ready.counter_at_end, Function.update_eq_self]
  have run := MachineUnaryCounter.guardInTime_zero Tape.counter
    (Driver.Label.guard : Driver.Label q) .tailStart .reverseOutput
    (Driver.program q) (Driver.program_guard q) base [] (normal relation flag).1 none
  simpa only [counterSelf, normal] using run

structure LoopResult (input : GenericGraphTables.Table q) (e remaining : Nat)
    (base : Tape → List Bool) (oldRelation : GenericGraphTables.RelationTable q)
    (oldFlag : Bool) where
  tapes : Tape → List Bool
  relation : GenericGraphTables.RelationTable q
  flag : Bool
  ready : LoopState.Ready input input.darts tapes
  run : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    ⟨some .guard, normal oldRelation oldFlag, base⟩
    (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
    (remaining * Body.bodyTime q (LoopState.inputBits input).length + 1)

def runRemaining (input : GenericGraphTables.Table q) :
    (remaining e : Nat) → e + remaining = input.darts →
    (base : Tape → List Bool) → LoopState.Ready input e base →
    (oldRelation : GenericGraphTables.RelationTable q) → (oldFlag : Bool) →
      LoopResult input e remaining base oldRelation oldFlag
  | 0, e, finished, base, ready, oldRelation, oldFlag => by
    have atEnd : e = input.darts := by omega
    subst e
    exact {
      tapes := base
      relation := oldRelation
      flag := oldFlag
      ready := ready
      run := by
        simpa only [Nat.zero_mul, Nat.zero_add] using
          zeroGuardInTime input base ready oldRelation oldFlag }
  | remaining + 1, e, finished, base, ready, oldRelation, oldFlag => by
    have beforeEnd : e < input.darts := by omega
    let edge : Fin input.darts := ⟨e, beforeEnd⟩
    let one := Body.rowStep input edge base ready oldRelation oldFlag
    let rest := runRemaining input remaining (e + 1) (by omega) one.tapes one.ready
      input.rows[edge].relation (CompareLoop.rowLoop input edge)
    let composed := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ one.run rest.run
    refine {
      tapes := rest.tapes
      relation := rest.relation
      flag := rest.flag
      ready := rest.ready
      run := { toEvalsTo := composed.toEvalsTo, steps_le_m := ?_ } }
    have budget := composed.steps_le_m
    simpa only [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using budget

def prefixTime (q N : Nat) : Nat :=
  Initialization.time N + N * Body.bodyTime q N + 1

structure PrefixResult (input : GenericGraphTables.Table q) where
  tapes : Tape → List Bool
  relation : GenericGraphTables.RelationTable q
  flag : Bool
  ready : LoopState.Ready input input.darts tapes
  run : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    (initList (Driver.machine q) (GenericGraphTables.tableBits input))
    (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
    (prefixTime q (LoopState.inputBits input).length)

def runPrefix (input : GenericGraphTables.Table q) : PrefixResult input := by
  let rows := runRemaining input input.darts 0 (by simp)
    (Initialization.loopTapes input) (LoopInitialization.initialization_ready input)
    (Vector.replicate (q * q) false) false
  let composed := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (Initialization.initializeInTime input) rows.run
  refine {
    tapes := rows.tapes
    relation := rows.relation
    flag := rows.flag
    ready := rows.ready
    run := { toEvalsTo := composed.toEvalsTo, steps_le_m := ?_ } }
  have budget := composed.steps_le_m
  change composed.steps ≤
    input.darts * Body.bodyTime q (LoopState.inputBits input).length + 1 +
      Initialization.time (LoopState.inputBits input).length at budget
  have rowCount : input.darts ≤ (LoopState.inputBits input).length :=
    GenericGraphTables.darts_le_tableBits_length input
  have rowBudget := Nat.mul_le_mul_right (Body.bodyTime q (LoopState.inputBits input).length)
    rowCount
  unfold prefixTime
  omega

theorem PrefixResult.reversed {input : GenericGraphTables.Table q} (result : PrefixResult input) :
    result.tapes .reversed = (GraphTables.tableBits (Table.build input)).reverse :=
  result.ready.reversed_at_end

theorem PrefixResult.output {input : GenericGraphTables.Table q} (result : PrefixResult input) :
    result.tapes .output = [] := result.ready.output

end DFVSGames.Foundations.PCP.AlphabetTable.Loop


namespace DFVSGames.Foundations.PCP.AlphabetTable.Finish

open Turing
open DFVSGames.Foundations.Complexity
open RuntimeModel
open scoped BigOperators

def afterReversal (base : Tape → List Bool) (word : List Bool) : Tape → List Bool :=
  Reduction.MachineTransfer.tapesAt .reversed .output base [] word

@[simp] theorem afterReversal_output (base : Tape → List Bool) (word : List Bool) :
    afterReversal base word .output = word := by
  simp [afterReversal, Reduction.MachineTransfer.tapesAt]

@[simp] theorem afterReversal_reversed (base : Tape → List Bool) (word : List Bool) :
    afterReversal base word .reversed = [] := by
  simp [afterReversal, Reduction.MachineTransfer.tapesAt]

def finishBudget (base : Tape → List Bool) (word : List Bool) : Nat :=
  word.length + 1 + (∑ i : Fin 15, (afterReversal base word (cleanupPorts i)).length) + 16

def reverseInTime (q : Nat) (base : Tape → List Bool) (word : List Bool)
    (state : State q) (hreversed : base .reversed = word.reverse)
    (houtput : base .output = []) :
    StateTransition.EvalsToInTime (Driver.machine q).step
      ⟨some .reverseOutput, state, base⟩
      (some ⟨some (.cleanup 0), (state.1, none), afterReversal base word⟩)
      (word.length + 1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (σ := Ambient q) Tape.reversed Tape.output (by decide) id false
    Driver.Label.reverseOutput (some (.cleanup 0)) (Driver.program q) rfl
    base state.1 state.2
  simp only [hreversed, houtput, List.length_reverse, List.reverse_reverse,
    List.map_id, List.append_nil] at run
  exact run

theorem cleared_eq_haltList (q : Nat) (base : Tape → List Bool) :
    (⟨none, initial q, Cleanup.clearTapes cleanupPorts base⟩ : (Driver.machine q).Cfg) =
      haltList (Driver.machine q) (base .output) := by
  have tapes := Cleanup.clearTapes_outputOnly cleanupPorts Tape.output base
    cleanupPorts_ne_output cleanupPorts_cover
  congr 1

def cleanupInTime (q : Nat) (base : Tape → List Bool) (state : State q) :
    StateTransition.EvalsToInTime (Driver.machine q).step
      ⟨some (.cleanup 0), state, base⟩
      (some (haltList (Driver.machine q) (base .output)))
      ((∑ i : Fin 15, (base (cleanupPorts i)).length) + 16) := by
  have run := Cleanup.cleanupInTime cleanupPorts Driver.Label.cleanup (initial q).1 none
    (Driver.program q)
    (fun i => by simp only [Driver.program, Cleanup.instruction_drain])
    (by simp only [Driver.program, Cleanup.instruction_finish]) base state.1 state.2
  change StateTransition.EvalsToInTime (Driver.machine q).step
    ⟨some (.cleanup 0), state, base⟩
    (some ⟨none, initial q, Cleanup.clearTapes cleanupPorts base⟩)
    ((∑ i : Fin 15, (base (cleanupPorts i)).length) + 15 + 1) at run
  rw [cleared_eq_haltList] at run
  simpa only [Nat.add_assoc] using run

def finishInTime (q : Nat) (base : Tape → List Bool) (word : List Bool)
    (state : State q) (hreversed : base .reversed = word.reverse)
    (houtput : base .output = []) :
    StateTransition.EvalsToInTime (Driver.machine q).step
      ⟨some .reverseOutput, state, base⟩
      (some (haltList (Driver.machine q) word)) (finishBudget base word) := by
  have first := reverseInTime q base word state hreversed houtput
  have last := cleanupInTime q (afterReversal base word) (state.1, none)
  rw [afterReversal_output] at last
  have run := StateTransition.EvalsToInTime.trans (Driver.machine q).step _ _
    ⟨some .reverseOutput, state, base⟩
    ⟨some (.cleanup 0), (state.1, none), afterReversal base word⟩
    (some (haltList (Driver.machine q) word)) first last
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have budgetEq : ((∑ i : Fin 15, (afterReversal base word (cleanupPorts i)).length) + 16) +
      (word.length + 1) =
      finishBudget base word := by
    dsimp only [finishBudget]
    omega
  exact run.steps_le_m.trans (Nat.le_of_eq budgetEq)

theorem afterReversal_selected_length_le (base : Tape → List Bool) (word : List Bool)
    (i : Fin 15) :
    (afterReversal base word (cleanupPorts i)).length ≤ (base (cleanupPorts i)).length := by
  have ho := cleanupPorts_ne_output i
  by_cases hr : cleanupPorts i = .reversed <;>
    simp [afterReversal, Reduction.MachineTransfer.tapesAt, ho, hr]

theorem stackLength_after_prefix (q : Nat) (input : List Bool)
    (base : Tape → List Bool) (state : State q) (budget : Nat)
    (prefixRun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) input) (some ⟨some .reverseOutput, state, base⟩) budget)
    (k : Tape) :
    (base k).length ≤ input.length + budget * Runtime.programPushBound (Driver.machine q) := by
  have bound := Runtime.executionSizeBound (Driver.machine q).step
    (fun cfg => (cfg.stk k).length) (Runtime.programPushBound (Driver.machine q))
    (Runtime.stepStackLength (Driver.machine q) k) prefixRun
  exact bound.trans (Nat.add_le_add_right
    (Runtime.initialStackLength (Driver.machine q) input k) _)

theorem finishBudget_le_of_prefix (q : Nat) (input : List Bool)
    (base : Tape → List Bool) (word : List Bool) (state : State q) (budget : Nat)
    (prefixRun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) input) (some ⟨some .reverseOutput, state, base⟩) budget)
    (hreversed : base .reversed = word.reverse) :
    finishBudget base word ≤
      16 * (input.length + budget * Runtime.programPushBound (Driver.machine q)) + 17 := by
  let B := input.length + budget * Runtime.programPushBound (Driver.machine q)
  have wordBound : word.length ≤ B := by
    simpa only [hreversed, List.length_reverse] using
      stackLength_after_prefix q input base state budget prefixRun .reversed
  have sumBound : (∑ i : Fin 15, (afterReversal base word (cleanupPorts i)).length) ≤ 15 * B := by
    calc
      _ ≤ ∑ _i : Fin 15, B := by
        apply Finset.sum_le_sum
        intro i _
        exact (afterReversal_selected_length_le base word i).trans
          (stackLength_after_prefix q input base state budget prefixRun (cleanupPorts i))
      _ = 15 * B := by simp
  dsimp only [finishBudget]
  omega

noncomputable def completedPolynomial (q : Nat) (prefixTime : Polynomial Nat) : Polynomial Nat :=
  prefixTime + Polynomial.C 16 *
    (Polynomial.X + Polynomial.C (Runtime.programPushBound (Driver.machine q)) * prefixTime) +
    Polynomial.C 17

def finishAfterPrefix (q : Nat) (input : List Bool) (base : Tape → List Bool)
    (word : List Bool) (state : State q) (budget : Nat)
    (prefixRun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) input) (some ⟨some .reverseOutput, state, base⟩) budget)
    (hreversed : base .reversed = word.reverse) (houtput : base .output = []) :
    TM2OutputsInTime (Driver.machine q) input (some word)
      (budget + 16 * (input.length + budget * Runtime.programPushBound (Driver.machine q)) + 17) := by
  have last := finishInTime q base word state hreversed houtput
  let run := StateTransition.EvalsToInTime.trans (Driver.machine q).step _ _
    (initList (Driver.machine q) input) ⟨some .reverseOutput, state, base⟩
    (some (haltList (Driver.machine q) word)) prefixRun last
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have finishBound := finishBudget_le_of_prefix q input base word state budget prefixRun hreversed
  have allBound := run.steps_le_m
  omega

def finishAfterPolynomialPrefix (q : Nat) (input : List Bool) (base : Tape → List Bool)
    (word : List Bool) (state : State q) (prefixTime : Polynomial Nat)
    (prefixRun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) input) (some ⟨some .reverseOutput, state, base⟩)
      (prefixTime.eval input.length))
    (hreversed : base .reversed = word.reverse) (houtput : base .output = []) :
    TM2OutputsInTime (Driver.machine q) input (some word)
      ((completedPolynomial q prefixTime).eval input.length) := by
  have run := finishAfterPrefix q input base word state (prefixTime.eval input.length)
    prefixRun hreversed houtput
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  simpa only [completedPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Nat.mul_comm] using run.steps_le_m

end DFVSGames.Foundations.PCP.AlphabetTable.Finish


namespace DFVSGames.Foundations.PCP.AlphabetTable.Runtime

open Turing
open DFVSGames.Foundations.Complexity
open RuntimeModel

noncomputable def prefixPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C 27 * Polynomial.X + Polynomial.C 54 +
    Polynomial.X *
      (Polynomial.C (32 + 8 * (Enumeration.localCount q * (6 * (2 * 4104)))) *
        (Polynomial.X + Polynomial.C 1)) + Polynomial.C 1

theorem prefixPolynomial_eval (q N : Nat) :
    (prefixPolynomial q).eval N = Loop.prefixTime q N := by
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Loop.prefixTime,
    Initialization.time, Body.bodyTime]
  ring

noncomputable def time (q : Nat) : Polynomial Nat :=
  Finish.completedPolynomial q (prefixPolynomial q)

noncomputable def tableOutputsInTime {q : Nat} (input : GenericGraphTables.Table q) :
    TM2OutputsInTime (Driver.machine q) (GenericGraphTables.tableBits input)
      (some (GraphTables.tableBits (Table.build input)))
      ((time q).eval (GenericGraphTables.tableBits input).length) := by
  let prefixRun := Loop.runPrefix input
  have hrun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some ⟨some .reverseOutput, normal prefixRun.relation prefixRun.flag, prefixRun.tapes⟩)
      ((prefixPolynomial q).eval (GenericGraphTables.tableBits input).length) := by
    rw [prefixPolynomial_eval]
    exact prefixRun.run
  exact Finish.finishAfterPolynomialPrefix q (GenericGraphTables.tableBits input)
    prefixRun.tapes (GraphTables.tableBits (Table.build input))
    (normal prefixRun.relation prefixRun.flag) (prefixPolynomial q) hrun
    prefixRun.ready.reversed_at_end prefixRun.ready.output

noncomputable def tablePolynomialTime (q : Nat) :
    TM2ComputableInPolyTime (GenericGraphTables.tableBits (q := q))
      GraphTables.tableBits (Table.build (q := q)) where
  tm := Driver.machine q
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time q
  outputsFun input := by
    dsimp only [Driver.machine, Equiv.refl]
    simp only [List.map_id]
    exact tableOutputsInTime input

end DFVSGames.Foundations.PCP.AlphabetTable.Runtime

end OAI
