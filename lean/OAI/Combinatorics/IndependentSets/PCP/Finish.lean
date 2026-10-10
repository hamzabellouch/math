import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.Driver

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Finish

open Turing
open IndependentSetsGames.Foundations.Complexity
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

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Finish

end OAI
