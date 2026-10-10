import Mathlib
import OAI.Computability.MinUncut.Machines.Driver

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.LoopInitialization

open MinUncutGames.Foundations.Complexity
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

end MinUncutGames.Foundations.PCP.AlphabetTable.LoopInitialization

end
section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.Loop

open Turing
open MinUncutGames.Foundations.Complexity
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

private noncomputable local instance prefixRunSizeOf (input : GenericGraphTables.Table q)
    (tapes : Tape → List Bool) (relation : GenericGraphTables.RelationTable q) (flag : Bool) :
    SizeOf (StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
      (prefixTime q (LoopState.inputBits input).length)) :=
  @StateTransition.EvalsToInTime._sizeOf_inst
    (TM2.Cfg Alphabet (Driver.Label q) (State q))
    (TM2.step (Driver.program q))
    (initList (Driver.machine q) (GenericGraphTables.tableBits input))
    (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
    (prefixTime q (LoopState.inputBits input).length) inferInstance

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

end MinUncutGames.Foundations.PCP.AlphabetTable.Loop

end
section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.Finish

open Turing
open MinUncutGames.Foundations.Complexity
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
  simpa only [hreversed, houtput, List.length_reverse, List.reverse_reverse,
    List.map_id, List.append_nil, afterReversal, Driver.machine, FinTM2.step] using! run

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

end MinUncutGames.Foundations.PCP.AlphabetTable.Finish

end
section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.Runtime

open Turing
open MinUncutGames.Foundations.Complexity
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
    change TM2OutputsInTime (Driver.machine q)
      ((GenericGraphTables.tableBits input).map id)
      (some ((GraphTables.tableBits (Table.build input)).map id)) _
    have input_eq : @List.map ((Driver.machine q).Γ (Driver.machine q).k₀)
        ((Driver.machine q).Γ (Driver.machine q).k₀) id
        (GenericGraphTables.tableBits input) = GenericGraphTables.tableBits input := List.map_id _
    have output_eq : @List.map ((Driver.machine q).Γ (Driver.machine q).k₁)
        ((Driver.machine q).Γ (Driver.machine q).k₁) id
        (GraphTables.tableBits (Table.build input)) =
        GraphTables.tableBits (Table.build input) := List.map_id _
    simpa only [input_eq, output_eq] using tableOutputsInTime input

end MinUncutGames.Foundations.PCP.AlphabetTable.Runtime

end
section
namespace MinUncutGames.Foundations.Complexity.MachineRepeat
open Turing

inductive ExtraTape
  | counter | temporary | output
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.counter, .temporary, .output]

protected theorem ExtraTape.enumList_getElem?_ctorIdx_eq (x : ExtraTape) :
    ExtraTape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide
inductive Phase
  | parse | guard | bodyToTemp | tempToBody | finalToTemp | tempToOutput
  deriving DecidableEq

protected abbrev Phase.enumList : List Phase := [.parse, .guard, .bodyToTemp, .tempToBody,
  .finalToTemp, .tempToOutput]

protected theorem Phase.enumList_getElem?_ctorIdx_eq (x : Phase) :
    Phase.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Phase.enumList_nodup : Phase.enumList.Nodup := by decide

instance : Fintype Phase where
  elems := ⟨Phase.enumList, Phase.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape (M : FinTM2) := M.K ⊕ ExtraTape
abbrev Symbols (M : FinTM2) := MachineEmbedding.Alphabet M.Γ (fun _ : ExtraTape => M.Γ M.k₀)
abbrev Label (M : FinTM2) := M.Λ ⊕ Phase
abbrev State (M : FinTM2) := M.σ × Option (M.Γ M.k₀)

def extraTapes (M : FinTM2) (counter temporary output : List (M.Γ M.k₀)) :
    ExtraTape → List (M.Γ M.k₀)
  | .counter => counter
  | .temporary => temporary
  | .output => output

def auxProgram (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool) :
    Phase → TM2.Stmt (Symbols M) (Label M) (State M)
  | .parse => .pop (.inl M.k₀) (fun s v => (s.1,v))
      (.branch (fun s => input (s.2.getD (input.symm false)))
        (.push (.inr .counter) (fun _ => input.symm true)
          (.load (fun s => (s.1,none)) (.goto (fun _ => .inr .parse))))
        (.load (fun s => (s.1,none)) (.goto (fun _ => .inr .guard))))
  | .guard => .pop (.inr .counter) (fun s v => (s.1,v))
      (.branch (fun s => s.2.isSome)
        (.load (fun s => (s.1,none)) (.goto (fun _ => .inl M.main)))
        (.load (fun s => (s.1,none)) (.goto (fun _ => .inr .finalToTemp))))
  | .bodyToTemp => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inl M.k₁) (.inr .temporary)
      (fun b => input.symm (output b)) (input.symm false)
      (.inr .bodyToTemp) (some (.inr .tempToBody))
  | .tempToBody => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inr .temporary) (.inl M.k₀)
      id (input.symm false) (.inr .tempToBody) (some (.inr .guard))
  | .finalToTemp => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inl M.k₀) (.inr .temporary)
      id (input.symm false) (.inr .finalToTemp) (some (.inr .tempToOutput))
  | .tempToOutput => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inr .temporary) (.inr .output)
      id (input.symm false) (.inr .tempToOutput) none

def program (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool) :
    Label M → TM2.Stmt (Symbols M) (Label M) (State M) :=
  MachineEmbedding.program (some (.inr .bodyToTemp)) M.m (auxProgram M input output)

def machine (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool) : FinTM2 where
  K := Tape M
  kFin := by letI := M.kFin; exact inferInstanceAs (Fintype (Tape M))
  k₀ := .inl M.k₀
  k₁ := .inr .output
  Γ := Symbols M
  Λ := Label M
  ΛFin := by letI := M.ΛFin; exact inferInstanceAs (Fintype (Label M))
  main := .inr .parse
  σ := State M
  σFin := by
    letI := M.σFin
    letI := M.Γk₀Fin
    exact inferInstanceAs (Fintype (State M))
  initialState := (M.initialState,none)
  Γk₀Fin := M.Γk₀Fin
  m := program M input output

def inputTapes (M : FinTM2) (word counter : List (M.Γ M.k₀)) : ∀k, List (Symbols M k) :=
  MachineEmbedding.tapes (initList M word).stk (extraTapes M counter [] [])

@[simp] theorem inputTapes_input (M : FinTM2) (word counter : List (M.Γ M.k₀)) :
    inputTapes M word counter (.inl M.k₀) = word := by
  simp [inputTapes, initList]

@[simp] theorem inputTapes_counter (M : FinTM2) (word counter : List (M.Γ M.k₀)) :
    inputTapes M word counter (.inr .counter) = counter := rfl

def inputConfig (M : FinTM2) (phase : Phase) (word counter : List (M.Γ M.k₀)) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  ⟨some (.inr phase),(M.initialState,none),inputTapes M word counter⟩

def embedded (M : FinTM2) (counter : List (M.Γ M.k₀)) (c : M.Cfg) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  MachineEmbedding.configuration (some (.inr .bodyToTemp)) (none : Option (M.Γ M.k₀))
    (extraTapes M counter [] []) c

def temporaryTapes (M : FinTM2) (word counter : List (M.Γ M.k₀)) : ∀k, List (Symbols M k) :=
  MachineEmbedding.tapes (fun _ => []) (extraTapes M counter word [])

def temporaryConfig (M : FinTM2) (phase : Phase) (word counter : List (M.Γ M.k₀)) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  ⟨some (.inr phase),(M.initialState,none),temporaryTapes M word counter⟩

private theorem inputTapes_update_input (M : FinTM2)
    (word counter replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word counter) (.inl M.k₀) replacement =
      inputTapes M replacement counter := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [inputTapes, initList]
    · simp [inputTapes, initList, h]
  | inr k => simp [inputTapes]

private theorem inputTapes_update_counter (M : FinTM2)
    (word counter replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word counter) (.inr .counter) replacement =
      inputTapes M word replacement := by
  funext k
  cases k with
  | inl k => simp [inputTapes]
  | inr k => cases k <;> simp [inputTapes, extraTapes]

def oneStep {α : Type*} (step : α → Option α) (a b : α)
    (h : step a = some b) : StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := by change step a = some b; exact h
  steps_le_m := le_refl _

variable (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool)

theorem parseStep_true (word counter : List (M.Γ M.k₀)) :
    (machine M input output).step
      (inputConfig M .parse (input.symm true :: word) counter) =
    some (inputConfig M .parse word (input.symm true :: counter)) := by
  change some (TM2.stepAux (auxProgram M input output .parse)
    (M.initialState,none) (inputTapes M (input.symm true :: word) counter)) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_input, inputTapes_update_counter,
    inputConfig]

theorem parseStep_false (word counter : List (M.Γ M.k₀)) :
    (machine M input output).step
      (inputConfig M .parse (input.symm false :: word) counter) =
    some (inputConfig M .guard word counter) := by
  change some (TM2.stepAux (auxProgram M input output .parse)
    (M.initialState,none) (inputTapes M (input.symm false :: word) counter)) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_input, inputTapes_update_counter,
    inputConfig]

theorem parseTrace (count : Nat) (word counter : List (M.Γ M.k₀)) :
    (MachineComposition.advance (machine M input output).step)^[count+1]
      (some (inputConfig M .parse ((encodeWord count).map input.symm ++ word) counter)) =
    some (inputConfig M .guard word (List.replicate count (input.symm true) ++ counter)) := by
  induction count generalizing counter with
  | zero =>
    simpa only [encodeWord, List.replicate_zero, List.nil_append, List.map_singleton,
      List.singleton_append, Nat.zero_add, Function.iterate_one, MachineComposition.advance_some]
      using! parseStep_false M input output word counter
  | succ count ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (machine M input output).step)^[count+1]
      ((machine M input output).step
        (inputConfig M .parse ((encodeWord (count+1)).map input.symm ++ word) counter)) = _
    simp only [encodeWord, List.replicate_succ, List.cons_append, List.map_cons,
      List.map_append, List.map_replicate]
    rw [parseStep_true]
    have h := ih (input.symm true :: counter)
    have hc : List.replicate count (input.symm true) ++ input.symm true :: counter =
        input.symm true :: (List.replicate count (input.symm true) ++ counter) := by
      rw [← List.singleton_append, ← List.append_assoc,
        ← List.replicate_succ', List.replicate_succ, List.cons_append]
    rw [hc] at h
    simpa only [encodeWord, List.map_append, List.map_replicate, List.map_singleton,
      List.map_nil, List.singleton_append, List.append_assoc] using! h

theorem guardStep_some (word counter : List (M.Γ M.k₀)) (symbol : M.Γ M.k₀) :
    (machine M input output).step (inputConfig M .guard word (symbol :: counter)) =
      some (embedded M counter (initList M word)) := by
  change some (TM2.stepAux (auxProgram M input output .guard)
    (M.initialState,none) (inputTapes M word (symbol :: counter))) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_counter,
    embedded, MachineEmbedding.configuration]
  exact ⟨rfl,rfl,rfl⟩

theorem guardStep_none (word : List (M.Γ M.k₀)) :
    (machine M input output).step (inputConfig M .guard word []) =
      some (inputConfig M .finalToTemp word []) := by
  change some (TM2.stepAux (auxProgram M input output .guard)
    (M.initialState,none) (inputTapes M word [])) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_counter, inputConfig]

def bodyExecution (counter : List (M.Γ M.k₀))
    (word : List (M.Γ M.k₀)) (result : List (M.Γ M.k₁)) (budget : Nat)
    (run : TM2OutputsInTime M word (some result) budget) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M counter (initList M word))
      (some (embedded M counter (haltList M result))) budget :=
  MachineComposition.embeddedExecution (some (.inr .bodyToTemp : Label M))
    (none : Option (M.Γ M.k₀)) (extraTapes M counter [] []) M.m
    (auxProgram M input output) run

private theorem bodyToTemp_tapes (result : List (M.Γ M.k₁)) (counter : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (.inl M.k₁) (.inr .temporary)
      (embedded M counter (haltList M result)).stk []
      (result.reverse.map (fun b => input.symm (output b))) =
    temporaryTapes M (result.reverse.map (fun b => input.symm (output b))) counter := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₁
    · subst k; simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]
    · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, embedded,
        MachineEmbedding.configuration, haltList, h]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, embedded,
      MachineEmbedding.configuration, extraTapes]

private theorem tempToBody_tapes (word counter : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inr .temporary) (.inl M.k₀)
      (temporaryTapes M word counter) [] word.reverse = inputTapes M word.reverse counter := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [Reduction.MachineTransfer.tapesAt, inputTapes, initList]
    · simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, initList, h]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, extraTapes]

private theorem finalToTemp_tapes (word : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inl M.k₀) (.inr .temporary)
      (inputTapes M word []) [] word.reverse = temporaryTapes M word.reverse [] := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]
    · simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, initList, h]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, extraTapes]

private theorem tempToOutput_tapes (word : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inr .temporary) (.inr .output)
      (temporaryTapes M word []) [] word.reverse =
        (haltList (machine M input output) word.reverse).stk := by
  funext k
  cases k with
  | inl k => simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, haltList, machine]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, haltList,
      machine, extraTapes]
    rfl

def bodyToTemp (result : List (M.Γ M.k₁)) (counter : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M counter (haltList M result))
      (some (temporaryConfig M .tempToBody
        (result.reverse.map (fun b => input.symm (output b))) counter)) (result.length+1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inl M.k₁) (.inr .temporary) (by intro h; cases h)
    (fun b => input.symm (output b)) (input.symm false)
    (.inr .bodyToTemp) (some (.inr .tempToBody)) (program M input output) rfl
    (embedded M counter (haltList M result)).stk M.initialState none
  have hs : (embedded M counter (haltList M result)).stk (.inl M.k₁) = result := by
    simp [embedded, MachineEmbedding.configuration, haltList]
  have hd : (embedded M counter (haltList M result)).stk (.inr .temporary) = [] := rfl
  rw [hs,hd,List.append_nil,bodyToTemp_tapes] at run
  exact run

def tempToBody (word counter : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (temporaryConfig M .tempToBody word counter)
      (some (inputConfig M .guard word.reverse counter)) (word.length+1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inr .temporary) (.inl M.k₀) (by intro h; cases h)
    id (input.symm false) (.inr .tempToBody) (some (.inr .guard))
    (program M input output) rfl (temporaryTapes M word counter) M.initialState none
  simp only [temporaryTapes, MachineEmbedding.tapes, extraTapes,
    List.map_id, List.append_nil] at run
  rw [show Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inr .temporary) (.inl M.k₀)
      (MachineEmbedding.tapes (fun _ => []) (extraTapes M counter word [])) [] word.reverse =
        inputTapes M word.reverse counter from tempToBody_tapes M word counter] at run
  exact run

def finalToTemp (word : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M .finalToTemp word [])
      (some (temporaryConfig M .tempToOutput word.reverse [])) (word.length+1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inl M.k₀) (.inr .temporary) (by intro h; cases h)
    id (input.symm false) (.inr .finalToTemp) (some (.inr .tempToOutput))
    (program M input output) rfl (inputTapes M word []) M.initialState none
  have hd : inputTapes M word [] (.inr .temporary) = [] := rfl
  rw [inputTapes_input,hd,List.map_id,List.append_nil,finalToTemp_tapes] at run
  exact run

def tempToOutput (word : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (temporaryConfig M .tempToOutput word [])
      (some (haltList (machine M input output) word.reverse)) (word.length+1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inr .temporary) (.inr .output) (by intro h; cases h)
    id (input.symm false) (.inr .tempToOutput) none
    (program M input output) rfl (temporaryTapes M word []) M.initialState none
  have hs : temporaryTapes M word [] (.inr .temporary) = word := rfl
  have hd : temporaryTapes M word [] (.inr .output) = [] := rfl
  rw [hs,hd,List.map_id,List.append_nil,tempToOutput_tapes] at run
  exact run

def bodyReturn (result : List (M.Γ M.k₁)) (counter : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M counter (haltList M result))
      (some (inputConfig M .guard (result.map (fun b => input.symm (output b))) counter))
      (2*(result.length+1)) := by
  have first := bodyToTemp M input output result counter
  have second := tempToBody M input output (result.reverse.map (fun b => input.symm (output b))) counter
  simp only [List.map_reverse,List.reverse_reverse,List.length_reverse,List.length_map] at first second
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  exact { toEvalsTo := full.toEvalsTo, steps_le_m := by have h := full.steps_le_m; omega }

def finish (word : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M .guard word []) (some (haltList (machine M input output) word))
      (2*word.length+3) := by
  have guard := oneStep _ _ _ (guardStep_none M input output word)
  have first := finalToTemp M input output word
  have second := tempToOutput M input output word.reverse
  simp only [List.reverse_reverse,List.length_reverse] at second
  have gfirst := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard first
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ gfirst second
  exact { toEvalsTo := full.toEvalsTo, steps_le_m := by have h := full.steps_le_m; omega }

def loopBudget : Nat → (Nat → List Bool) → (Nat → Nat) → Nat
  | 0, words, _ => 2*(words 0).length+3
  | count+1, words, budgets => budgets 0 + 2*(words 1).length+3 +
      loopBudget count (fun i => words (i+1)) (fun i => budgets (i+1))

def loopExecution (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (runs : ∀ i, i < count → TM2OutputsInTime M ((words i).map input.symm)
      (some ((words (i+1)).map output.symm)) (budgets i)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M .guard ((words 0).map input.symm)
        (List.replicate count (input.symm true)))
      (some (haltList (machine M input output) ((words count).map input.symm)))
      (loopBudget count words budgets) := by
  induction count generalizing words budgets with
  | zero =>
    simpa only [loopBudget,List.replicate_zero,List.length_map] using!
      finish M input output ((words 0).map input.symm)
  | succ count ih =>
    rw [List.replicate_succ]
    have guard := oneStep _ _ _ (guardStep_some M input output ((words 0).map input.symm)
      (List.replicate count (input.symm true)) (input.symm true))
    have body := bodyExecution M input output (List.replicate count (input.symm true))
      ((words 0).map input.symm) ((words 1).map output.symm) (budgets 0)
      (runs 0 (Nat.zero_lt_succ count))
    have returned := bodyReturn M input output ((words 1).map output.symm)
      (List.replicate count (input.symm true))
    have handoff : ((words 1).map output.symm).map (fun b => input.symm (output b)) =
        (words 1).map input.symm := by
      simp only [List.map_map,Function.comp_def,Equiv.apply_symm_apply]
    rw [handoff,List.length_map] at returned
    have tail := ih (fun i => words (i+1)) (fun i => budgets (i+1))
      (fun i hi => runs (i+1) (Nat.succ_lt_succ hi))
    have first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard body
    have second := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first returned
    have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ second tail
    exact {
      toEvalsTo := full.toEvalsTo
      steps_le_m := by
        have h := full.steps_le_m
        simp only [loopBudget]
        omega
    }

private theorem inputConfig_init (word : List (M.Γ M.k₀)) :
    inputConfig M .parse word [] = initList (machine M input output) word := by
  unfold inputConfig initList
  congr 1
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [inputTapes,initList,machine]; rfl
    · simp [inputTapes,initList,machine,h]
  | inr k => cases k <;> simp [inputTapes,initList,machine,extraTapes]

def executeSequence (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (runs : ∀ i, i < count → TM2OutputsInTime M ((words i).map input.symm)
      (some ((words (i+1)).map output.symm)) (budgets i)) :
    TM2OutputsInTime (machine M input output)
      ((encodeWord count ++ words 0).map input.symm)
      (some ((words count).map input.symm))
      (count+1 + loopBudget count words budgets) := by
  let parsed : StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M .parse ((encodeWord count).map input.symm ++ (words 0).map input.symm) [])
      (some (inputConfig M .guard ((words 0).map input.symm)
        (List.replicate count (input.symm true)))) (count+1) := {
    steps := count+1
    evals_in_steps := by
      change (MachineComposition.advance (machine M input output).step)^[count+1]
        (some (inputConfig M .parse ((encodeWord count).map input.symm ++ (words 0).map input.symm) [])) = _
      simpa only [List.append_nil] using! parseTrace M input output count
        ((words 0).map input.symm) []
    steps_le_m := le_refl _
  }
  have body := loopExecution M input output count words budgets runs
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ parsed body
  rw [inputConfig_init M input output] at full
  erw [List.map_append]
  simpa only [TM2OutputsInTime,Option.map_some,Nat.add_comm] using! full

omit M input output in

theorem loopBudget_eq_sum (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat) :
    loopBudget count words budgets =
      (∑ i ∈ Finset.range count, (budgets i + 2*(words (i+1)).length+3)) +
      2*(words count).length+3 := by
  induction count generalizing words budgets with
  | zero => simp [loopBudget]
  | succ count ih =>
    rw [loopBudget, ih, Finset.sum_range_succ']
    simp only [Nat.zero_add]
    omega

def executeSequenceSum (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (runs : ∀ i, i < count → TM2OutputsInTime M ((words i).map input.symm)
      (some ((words (i+1)).map output.symm)) (budgets i)) :
    TM2OutputsInTime (machine M input output)
      ((encodeWord count ++ words 0).map input.symm)
      (some ((words count).map input.symm))
      (count+1 + ((∑ i ∈ Finset.range count, (budgets i+2*(words (i+1)).length+3)) +
        2*(words count).length+3)) := by
  rw [← loopBudget_eq_sum]
  exact executeSequence M input output count words budgets runs

omit M input output in

theorem loopBudget_le (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (bodyBound lengthBound : Nat)
    (hb : ∀i, i<count → budgets i ≤ bodyBound)
    (hl : ∀i, i≤count → (words i).length ≤ lengthBound) :
    loopBudget count words budgets ≤ count*(bodyBound+2*lengthBound+3)+2*lengthBound+3 := by
  rw [loopBudget_eq_sum]
  have hs : (∑ i ∈ Finset.range count, (budgets i+2*(words (i+1)).length+3)) ≤
      count*(bodyBound+2*lengthBound+3) := by
    calc
      _ ≤ ∑ i ∈ Finset.range count, (bodyBound+2*lengthBound+3) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hbi := hb i hi'
        have hli := hl (i+1) hi'
        omega
      _ = _ := by simp
  have hlast := hl count (le_refl _)
  omega

end MinUncutGames.Foundations.Complexity.MachineRepeat

end

end OAI
