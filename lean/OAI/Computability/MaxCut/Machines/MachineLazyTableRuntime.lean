import Mathlib
import OAI.Computability.MaxCut.Machines.MachineLazyTable

namespace OAI

/-!
Canonical polynomial-time computation of the executable lazy preprocessing map.
The raw machine's retained original input is physically drained by the checked
canonical-output wrapper before it reaches the standard `haltList` endpoint.
-/

namespace MaxCutGames.Foundations.Complexity.MachineLazyTableRuntime

open Turing PCP
open MachineLazyTable (Tape Label State)

def rawProgram (d : Nat) (positive : 0 < d) :
    MachineCanonicalOutput.Program Tape (Label d) (State d) where
  input := .input
  output := .output
  main := .split .copyFirst
  initial := MachineLazyTable.clean d positive
  code := MachineLazyTable.program d positive

theorem sourceMachine_eq (d : Nat) (positive : 0 < d) :
    MachineCanonicalOutput.sourceMachine (rawProgram d positive) =
      MachineLazyTable.machine d positive := rfl

/-- A fixed explicit list of every non-output tape, independent of input data. -/
def cleanupTapes : List Tape :=
  [.input, .source, .vertices, .darts, .fuel, .vertex, .reverse,
    .tail, .old, .relation, .scratch, .divided, .quotient, .newReverse, .rowBuffer]

theorem cleanup_complete (d : Nat) (positive : 0 < d) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram d positive).output := by
  cases k <;> simp [cleanupTapes, rawProgram]

/-- The terminal witness is the checked full lazy-table execution. The wrapper
then drains the retained original input rather than assuming it disappeared. -/
def terminalRun (d : Nat) (positive : 0 < d) (a : PortTables.Input d) :
    MachineCanonicalOutput.TerminalRun (rawProgram d positive) (PortTables.inputBits a)
      (PortTables.inputBits (PreprocessingStageMaps.lazy d a))
      ((MachineLazyTable.timePolynomial d).eval (PortTables.inputBits a).length) where
  state := MachineLazyTable.clean d positive
  tapes := MachineLazyTable.finalTapes (PortTables.inputBits a)
    (PortTables.inputBits (PreprocessingStageMaps.lazy d a))
  execution := MachineLazyTable.machineInTime a.2 positive
  output_eq := rfl

/-- The actual canonical-output finite machine computes precisely the shared
degree-d to degree-2d stage map in polynomial time. -/
noncomputable def computableInPolyTime (d : Nat) (positive : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := 2 * d)) (PreprocessingStageMaps.lazy d) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram d positive) cleanupTapes
    (cleanup_complete d positive) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.lazy d) (MachineLazyTable.timePolynomial d) (terminalRun d positive)

/-- Every tape alphabet of this exact completed computation certificate is finite. -/
theorem finite_alphabet (d : Nat) (positive : 0 < d) :
    ∀ k, Finite ((computableInPolyTime d positive).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram d positive) cleanupTapes
    (cleanup_complete d positive) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.lazy d) (MachineLazyTable.timePolynomial d) (terminalRun d positive)

end MaxCutGames.Foundations.Complexity.MachineLazyTableRuntime

/-! The actual padding, expander overlay, and lazy-loop stages composed into
one polynomial-time finite machine. The initial degree-replacement stage is
assembled separately. -/
namespace MaxCutGames.Foundations.PCP.PreprocessingFinishRuntime

open Turing MaxCutGames.Foundations.Complexity
open PreprocessingRegularTables

def finish (H : PreprocessingTables.BaseTable) (d : Nat) (input : PortTables.Input d) :
    PortTables.Input (2 * (d + internalDegree)) :=
  PreprocessingStageMaps.lazy (d + internalDegree)
    (PreprocessingStageMaps.paddedOverlay H d input)

theorem output_eq_finish (H : PreprocessingTables.BaseTable) (t : GraphTables.Table) :
    PreprocessingTables.output H t =
      finish H (internalDegree + 1) (PreprocessingStageMaps.regular H t) := rfl

theorem finish_degree_positive (d : Nat) (hd : 0 < d) : 0 < d + internalDegree :=
  hd.trans_le (Nat.le_add_right d internalDegree)

/-- Both stages supply complete executions, cleanup, and polynomial bounds;
the sequential composition includes the physical interstage bit transfer. -/
noncomputable def computableInPolyTime (H : PreprocessingTables.BaseTable)
    (d : Nat) (hd : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := 2 * (d + internalDegree))) (finish H d) := by
  change TM2ComputableInPolyTime _ _
    (fun input => PreprocessingStageMaps.lazy (d + internalDegree)
      (PreprocessingStageMaps.paddedOverlay H d input))
  exact MachineSequential.composeBits (MachinePaddedOverlayRuntime.computableInPolyTime H d hd)
    (MachineLazyTableRuntime.computableInPolyTime (d + internalDegree)
      (finish_degree_positive d hd))

theorem finite_alphabet (H : PreprocessingTables.BaseTable) (d : Nat) (hd : 0 < d) :
    MachineFiniteAlphabet.FiniteAlphabet (computableInPolyTime H d hd).tm :=
  MachineFiniteAlphabet.composeBits
    (MachinePaddedOverlayRuntime.computableInPolyTime H d hd)
    (MachineLazyTableRuntime.computableInPolyTime (d + internalDegree)
      (finish_degree_positive d hd))
    (MachinePaddedOverlayRuntime.finite_alphabet H d hd)
    (MachineLazyTableRuntime.finite_alphabet (d + internalDegree)
      (finish_degree_positive d hd))

end MaxCutGames.Foundations.PCP.PreprocessingFinishRuntime

/-! The complete actual preprocessing machine, including degree replacement,
vertex padding, explicit expander construction, overlay, and lazy edges. -/
namespace MaxCutGames.Foundations.PCP.PreprocessingRuntime
open Turing MaxCutGames.Foundations.Complexity
open PreprocessingRegularTables

noncomputable def tablePolynomialTime (H : PreprocessingTables.BaseTable) :
    TM2ComputableInPolyTime GraphTables.tableBits
      (PortTables.inputBits (ports := PreprocessingTables.degree))
      (PreprocessingTables.output H) := by
  change TM2ComputableInPolyTime GraphTables.tableBits
    (PortTables.inputBits (ports := 2 * ((internalDegree + 1) + internalDegree)))
    (fun t => PreprocessingFinishRuntime.finish H (internalDegree + 1)
      (PreprocessingStageMaps.regular H t))
  exact MachineSequential.composeBits
    (MachineRegularTableRuntime.computableInPolyTime H)
    (PreprocessingFinishRuntime.computableInPolyTime H (internalDegree + 1)
      (Nat.succ_pos internalDegree))

theorem finiteAlphabet (H : PreprocessingTables.BaseTable) :
    MachineFiniteAlphabet.FiniteAlphabet (tablePolynomialTime H).tm :=
  MachineFiniteAlphabet.composeBits
    (MachineRegularTableRuntime.computableInPolyTime H)
    (PreprocessingFinishRuntime.computableInPolyTime H (internalDegree + 1)
      (Nat.succ_pos internalDegree))
    (MachineRegularTableRuntime.finite_alphabet H)
    (PreprocessingFinishRuntime.finite_alphabet H (internalDegree + 1)
      (Nat.succ_pos internalDegree))

end MaxCutGames.Foundations.PCP.PreprocessingRuntime

/-!
An actual logarithmic-round counter. Unary input is stripped to a raw tally;
each positive round emits one tally and halves the remaining input by pairing
symbols. The zero input emits one round explicitly. All tapes except the
canonical output are empty at termination.
-/

namespace MaxCutGames.Foundations.Complexity.MachineLogCounter

open Turing

def bitLength (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

@[simp] theorem bitLength_zero : bitLength 0 = 0 := rfl

theorem bitLength_positive {n : Nat} (h : n ≠ 0) : bitLength n = n.log2 + 1 := by
  simp [bitLength, h]

theorem bitLength_half {n : Nat} (h : n ≠ 0) : bitLength n = bitLength (n / 2) + 1 := by
  by_cases hone : n = 1
  · subst n; rfl
  have hn : 2 ≤ n := by omega
  have hh : n / 2 ≠ 0 := by omega
  rw [bitLength_positive h, bitLength_positive hh, Nat.log2_def n, ite_eq_left hn]

def increments (n : Nat) (started : Bool) : Nat :=
  if n = 0 then (if started then 0 else 1) else bitLength n

@[simp] theorem increments_true (n : Nat) : increments n true = bitLength n := by
  by_cases hn : n = 0 <;> simp [increments, hn]

theorem increments_half {n : Nat} (h : n ≠ 0) (started : Bool) :
    increments n started = increments (n / 2) true + 1 := by
  rw [increments, ite_eq_right h, increments_true, bitLength_half h]

theorem increments_false (n : Nat) : increments n false = n.log2 + 1 := by
  by_cases hn : n = 0
  · subst n; rfl
  · simp [increments, bitLength, hn]

def coreTime (n : Nat) : Nat :=
  if h : n = 0 then 1 else n + n / 2 + 3 + coreTime (n / 2)
termination_by n
decreasing_by omega

@[simp] theorem coreTime_zero : coreTime 0 = 1 := by rw [coreTime]; rfl

theorem coreTime_positive {n : Nat} (h : n ≠ 0) :
    coreTime n = n + n / 2 + 3 + coreTime (n / 2) := by
  rw [coreTime, dite_eq_right h]

theorem coreTime_bound (n : Nat) : coreTime n ≤ 6 * n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; simp
    · rw [coreTime_positive hn]
      have smaller : n / 2 < n := by omega
      have bound := ih (n / 2) smaller
      omega

abbrev Alphabet (_ : Fin 3) := Bool
abbrev State := (Bool × Bool) × Option Bool

def initialState : State := ((false, false), none)

def rawTapes (input scratch output : List Bool) : Fin 3 → List Bool
  | 0 => input
  | 1 => scratch
  | 2 => output

private theorem update_input_inline_MachineLogCounter (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 0 replacement = rawTapes replacement scratch output := by
  funext k
  fin_cases k <;> rfl

private theorem update_scratch_inline_MachineLogCounter (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 1 replacement = rawTapes input replacement output := by
  funext k
  fin_cases k <;> rfl

private theorem update_output_inline_MachineLogCounter (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 2 replacement = rawTapes input scratch replacement := by
  funext k
  fin_cases k <;> rfl

def stripLoop : TM2.Stmt Alphabet (Fin 5) State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push 1 (fun _ => true) (.goto fun _ => (1 : Fin 5)))
      (.load (fun _ => initialState) (.goto fun _ => 4)))

def guardLoop : TM2.Stmt Alphabet (Fin 5) State :=
  .peek 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push 2 (fun _ => true)
        (.load (fun _ => ((false, true), none)) (.goto fun _ => 3)))
      (.branch (fun state => state.1.2)
        (.load (fun _ => initialState) .halt)
        (.push 2 (fun _ => true) (.load (fun _ => initialState) .halt))))

def halfLoop : TM2.Stmt Alphabet (Fin 5) State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.branch (fun state => state.1.1)
        (.push 1 (fun _ => true)
          (.load (fun state => ((false, state.1.2), state.2)) (.goto fun _ => 3)))
        (.load (fun state => ((true, state.1.2), state.2)) (.goto fun _ => 3)))
      (.load (fun state => ((false, state.1.2), none)) (.goto fun _ => 4)))

def program : Fin 5 → TM2.Stmt Alphabet (Fin 5) State
  | 0 => .push 2 (fun _ => false) (.goto fun _ => 1)
  | 1 => stripLoop
  | 2 => guardLoop
  | 3 => halfLoop
  | 4 => Reduction.MachineTransfer.loopAt 1 0 id false 4 (some 2)

def machine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ := Alphabet
  Λ := Fin 5
  main := 0
  σ := State
  initialState := initialState
  m := program

def configuration (label : Option (Fin 5)) (state : State)
    (input scratch output : List Bool) : machine.Cfg :=
  ⟨label, state, rawTapes input scratch output⟩

def next := MachineComposition.advance machine.step

theorem stripStep_true (input scratch output : List Bool) (state : State) :
    machine.step (configuration (some 1) state (true :: input) scratch output) =
      some (configuration (some 1) (state.1, some true) input (true :: scratch) output) := by
  change some (TM2.stepAux stripLoop state (rawTapes (true :: input) scratch output)) = _
  simp [stripLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_input_inline_MachineLogCounter, update_scratch_inline_MachineLogCounter]
  rfl

theorem stripStep_false (scratch output : List Bool) (state : State) :
    machine.step (configuration (some 1) state [false] scratch output) =
      some (configuration (some 4) initialState [] scratch output) := by
  change some (TM2.stepAux stripLoop state (rawTapes [false] scratch output)) = _
  simp [stripLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_input_inline_MachineLogCounter]
  rfl

theorem stripTrace (n : Nat) (scratch output : List Bool) (state : State) :
    next^[n + 1] (some (configuration (some 1) state (encodeWord n) scratch output)) =
      some (configuration (some 4) initialState [] (List.replicate n true ++ scratch) output) := by
  induction n generalizing scratch state with
  | zero =>
    simpa only [encodeWord, List.replicate_zero, List.nil_append, Nat.zero_add,
      Function.iterate_one, next, MachineComposition.advance_some] using
      stripStep_false scratch output state
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change next^[n + 1]
      (machine.step (configuration (some 1) state (true :: encodeWord n) scratch output)) = _
    rw [stripStep_true, ih]
    congr 2
    simp only [List.replicate_add, List.replicate_one, List.append_assoc, List.singleton_append]

theorem halfStep_nil (scratch output : List Bool) (parity started : Bool) (register : Option Bool) :
    machine.step (configuration (some 3) ((parity, started), register) [] scratch output) =
      some (configuration (some 4) ((false, started), none) [] scratch output) := by
  change some (TM2.stepAux halfLoop ((parity, started), register) (rawTapes [] scratch output)) = _
  simp [halfLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_input_inline_MachineLogCounter]
  rfl

theorem halfStep_false (input scratch output : List Bool) (started : Bool) (register : Option Bool) :
    machine.step (configuration (some 3) ((false, started), register) (true :: input) scratch output) =
      some (configuration (some 3) ((true, started), some true) input scratch output) := by
  change some (TM2.stepAux halfLoop ((false, started), register)
    (rawTapes (true :: input) scratch output)) = _
  simp [halfLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_input_inline_MachineLogCounter]
  rfl

theorem halfStep_true (input scratch output : List Bool) (started : Bool) (register : Option Bool) :
    machine.step (configuration (some 3) ((true, started), register) (true :: input) scratch output) =
      some (configuration (some 3) ((false, started), some true) input (true :: scratch) output) := by
  change some (TM2.stepAux halfLoop ((true, started), register)
    (rawTapes (true :: input) scratch output)) = _
  simp [halfLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_input_inline_MachineLogCounter, update_scratch_inline_MachineLogCounter]
  rfl

/-- A parity bit implements division by two using actual pop/push transitions. -/
theorem halfTrace (n m : Nat) (output : List Bool) (parity started : Bool)
    (register : Option Bool) :
    next^[n + 1] (some (configuration (some 3) ((parity, started), register)
      (List.replicate n true) (List.replicate m true) output)) =
      some (configuration (some 4) ((false, started), none) []
        (List.replicate (m + (n + if parity then 1 else 0) / 2) true) output) := by
  induction n generalizing m parity register with
  | zero =>
    cases parity <;>
      simpa only [Nat.zero_add, Function.iterate_one, next, MachineComposition.advance_some,
        List.replicate_zero, Bool.false_eq_true, ite_false, ite_true, Nat.zero_div,
        Nat.add_zero, Nat.reduceDiv] using
        halfStep_nil (List.replicate m true) output _ started register
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change next^[n + 1]
      (machine.step (configuration (some 3) ((parity, started), register)
        (true :: List.replicate n true) (List.replicate m true) output)) = _
    cases parity with
    | false =>
      rw [halfStep_false, ih]
      congr 2
    | true =>
      rw [halfStep_true]
      change next^[n + 1] (some (configuration (some 3) ((false, started), some true)
        (List.replicate n true) (List.replicate (m + 1) true) output)) = _
      rw [ih]
      congr 2
      congr 1
      change m + 1 + n / 2 = m + (n + 1 + 1) / 2
      omega

theorem restoreTrace (n : Nat) (output : List Bool) (started : Bool) :
    next^[n + 1] (some (configuration (some 4) ((false, started), none)
      [] (List.replicate n true) output)) =
      some (configuration (some 2) ((false, started), none) (List.replicate n true) [] output) := by
  have run := Reduction.MachineTransfer.transferAt_fromTapes (1 : Fin 3) 0 (by decide)
    id false (4 : Fin 5) (some 2) program rfl
    (rawTapes [] (List.replicate n true) output) (false, started) none
  simp only [rawTapes, List.length_replicate, List.reverse_replicate, List.map_id,
    List.append_nil] at run
  have tapesEq : Reduction.MachineTransfer.tapesAt (1 : Fin 3) 0
      (rawTapes [] (List.replicate n true) output) [] (List.replicate n true) =
      rawTapes (List.replicate n true) [] output := by
    funext k
    fin_cases k <;> rfl
  rw [tapesEq] at run
  exact run

theorem guardStep_zero (output : List Bool) (started : Bool) :
    machine.step (configuration (some 2) ((false, started), none) [] [] output) =
      some (configuration none initialState [] [] (if started then output else true :: output)) := by
  change some (TM2.stepAux guardLoop ((false, started), none) (rawTapes [] [] output)) = _
  cases started <;> simp [guardLoop, TM2.stepAux, rawTapes, configuration]
  all_goals try rw [update_output_inline_MachineLogCounter]
  all_goals rfl

theorem guardStep_positive (n : Nat) (output : List Bool) (started : Bool) :
    machine.step (configuration (some 2) ((false, started), none)
      (List.replicate (n + 1) true) [] output) =
      some (configuration (some 3) ((false, true), none)
        (List.replicate (n + 1) true) [] (true :: output)) := by
  change some (TM2.stepAux guardLoop ((false, started), none)
    (rawTapes (true :: List.replicate n true) [] output)) = _
  simp [guardLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_output_inline_MachineLogCounter]
  simp only [List.replicate_succ]
  rfl

/-- The halving rounds are actual guard, scan, and restoration executions. -/
theorem coreTrace (n : Nat) (output : List Bool) (started : Bool) :
    next^[coreTime n] (some (configuration (some 2) ((false, started), none)
      (List.replicate n true) [] output)) =
      some (configuration none initialState [] []
        (List.replicate (increments n started) true ++ output)) := by
  induction n using Nat.strong_induction_on generalizing output started with
  | h n ih =>
    cases n with
    | zero =>
      cases started with
      | false => simpa [increments, next, MachineComposition.advance] using! guardStep_zero output false
      | true => simpa [increments, next, MachineComposition.advance] using! guardStep_zero output true
    | succ n =>
      have nonzero : n + 1 ≠ 0 := by omega
      have smaller : (n + 1) / 2 < n + 1 := by omega
      have recursive := ih ((n + 1) / 2) smaller (true :: output) true
      have half := halfTrace (n + 1) 0 (true :: output) false true none
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.zero_add,
        List.replicate_zero] at half
      have restore := restoreTrace ((n + 1) / 2) (true :: output) true
      rw [coreTime_positive nonzero]
      rw [show n + 1 + (n + 1) / 2 + 3 + coreTime ((n + 1) / 2) =
        (coreTime ((n + 1) / 2) + ((n + 1) / 2 + 1) + (n + 1 + 1)) + 1 by omega,
        Function.iterate_succ_apply]
      change next^[coreTime ((n + 1) / 2) + ((n + 1) / 2 + 1) + (n + 1 + 1)]
        (machine.step (configuration (some 2) ((false, started), none)
          (List.replicate (n + 1) true) [] output)) = _
      rw [guardStep_positive, Function.iterate_add_apply, half,
        Function.iterate_add_apply, restore, recursive]
      rw [increments_half nonzero started]
      simp only [List.replicate_add, List.replicate_one, List.append_assoc, List.singleton_append]

theorem initList_eq (input : List Bool) :
    initList machine input = configuration (some 0) initialState input [] [] := by
  simp only [machine]
  unfold initList configuration
  congr 1
  funext k
  change Fin 3 at k
  fin_cases k <;> rfl

theorem haltList_eq (output : List Bool) :
    haltList machine output = configuration none initialState [] [] output := by
  unfold haltList configuration
  congr 1
  funext k
  change Fin 3 at k
  fin_cases k <;> rfl

theorem initialStep (input : List Bool) :
    machine.step (configuration (some 0) initialState input [] []) =
      some (configuration (some 1) initialState input [] [false]) := by
  change some (TM2.stepAux (.push (2 : Fin 3) (fun _ : State => false) (.goto fun _ => (1 : Fin 5)))
    initialState (rawTapes input [] [])) = _
  simp only [TM2.stepAux, rawTapes]
  rw [update_output_inline_MachineLogCounter]
  rfl

def totalTime (n : Nat) : Nat := 2 * n + 3 + coreTime n

theorem totalTime_bound (n : Nat) : totalTime n ≤ 8 * n + 4 := by
  have bound := coreTime_bound n
  unfold totalTime
  omega

theorem machineTrace (n : Nat) :
    next^[totalTime n] (some (initList machine (encodeWord n))) =
      some (haltList machine (encodeWord (n.log2 + 1))) := by
  rw [initList_eq, haltList_eq]
  rw [show totalTime n = (coreTime n + (n + 1) + (n + 1)) + 1 by
    unfold totalTime; omega, Function.iterate_succ_apply]
  change next^[coreTime n + (n + 1) + (n + 1)]
    (machine.step (configuration (some 0) initialState (encodeWord n) [] [])) = _
  rw [initialStep, Function.iterate_add_apply, stripTrace]
  simp only [List.append_nil]
  rw [Function.iterate_add_apply]
  dsimp only [initialState]
  rw [restoreTrace n [false] false, coreTrace, increments_false]
  rfl

def outputsInTime (n : Nat) :
    TM2OutputsInTime machine (encodeWord n) (some (encodeWord (n.log2 + 1))) (8 * n + 4) where
  steps := totalTime n
  evals_in_steps := machineTrace n
  steps_le_m := totalTime_bound n

/-- A genuine finite-machine certificate for unary `log2(n)+1`; its linear
polynomial is measured in the actual encoded input length. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeWord encodeWord (fun n => n.log2 + 1) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 8 * Polynomial.X + 4
  outputsFun n := by
    change TM2OutputsInTime machine ((encodeWord n).map id)
      (some ((encodeWord (n.log2 + 1)).map id))
      ((8 * Polynomial.X + 4 : Polynomial Nat).eval (encodeWord n).length)
    have hi := @List.map_id (machine.Γ machine.k₀) (encodeWord n)
    have ho := @List.map_id (machine.Γ machine.k₁) (encodeWord (n.log2 + 1))
    rw [hi, ho]
    have execution := outputsInTime n
    refine {
      toEvalsTo := execution.toEvalsTo
      steps_le_m := Nat.le_trans execution.steps_le_m ?_
    }
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    simp [encodeWord]

end MaxCutGames.Foundations.Complexity.MachineLogCounter

/-! A fixed Boolean-stack program prepending the logarithmic round count to
a graph table. It copies the original word, adds its two unary header values,
runs the actual logarithm machine, then emits the counter and original word. -/

namespace MaxCutGames.Foundations.Complexity.GraphCounterModel

open Turing

inductive ExtraTape
  | input | archive | scratch | output
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.input, .archive, .scratch, .output]

protected theorem ExtraTape.enumList_getElem?_ctorIdx_eq (x : ExtraTape) :
    ExtraTape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive ExtraLabel
  | copyFirst | copySecond | seed | headerFirst | headerSecond
  | clearInput | clockCopy | archiveCopy | finalReverse
  deriving DecidableEq

protected abbrev ExtraLabel.enumList : List ExtraLabel := [.copyFirst, .copySecond, .seed,
  .headerFirst, .headerSecond, .clearInput, .clockCopy, .archiveCopy, .finalReverse]

protected theorem ExtraLabel.enumList_getElem?_ctorIdx_eq (x : ExtraLabel) :
    ExtraLabel.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem ExtraLabel.enumList_nodup : ExtraLabel.enumList.Nodup := by decide

instance : Fintype ExtraLabel where
  elems := ⟨ExtraLabel.enumList, ExtraLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := Fin 3 ⊕ ExtraTape
abbrev Label := Fin 5 ⊕ ExtraLabel
abbrev Alphabet (_ : Tape) := Bool
abbrev State := MachineLogCounter.State × Option Bool

def initialState : State := (MachineLogCounter.initialState, none)

def clockLabel : Option (Fin 5) → Option Label
  | none => some (.inr .clearInput)
  | some l => some (.inl l)

/-- Homogeneous Boolean embedding of the fixed logarithm program. -/
def clockStatement : TM2.Stmt MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State →
    TM2.Stmt Alphabet Label State
  | .push k f next => .push (.inl k) (fun state => f state.1) (clockStatement next)
  | .peek k f next => .peek (.inl k) (fun state x => (f state.1 x, state.2)) (clockStatement next)
  | .pop k f next => .pop (.inl k) (fun state x => (f state.1 x, state.2)) (clockStatement next)
  | .load f next => .load (fun state => (f state.1, state.2)) (clockStatement next)
  | .branch f yes no => .branch (fun state => f state.1) (clockStatement yes) (clockStatement no)
  | .goto f => .goto (fun state => .inl (f state.1))
  | .halt => .goto (fun _ => .inr .clearInput)

def readHeader (again next : Label) : TM2.Stmt Alphabet Label State :=
  .pop (.inr .input) (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push (.inl 0) (fun _ => true) (.goto fun _ => again))
      (.load (fun state => (state.1, none)) (.goto fun _ => next)))

def program : Label → TM2.Stmt Alphabet Label State
  | .inl l => clockStatement (MachineLogCounter.program l)
  | .inr .copyFirst => Reduction.MachineTransfer.loopAt (.inr .input) (.inr .scratch)
      id false (.inr .copyFirst) (some (.inr .copySecond))
  | .inr .copySecond => MachineCopy.forkLoop (.inr .scratch) (.inr .input) (.inr .archive)
      false (.inr .copySecond) (some (.inr .seed))
  | .inr .seed => .push (.inl 0) (fun _ => false) (.goto fun _ => .inr .headerFirst)
  | .inr .headerFirst => readHeader (.inr .headerFirst) (.inr .headerSecond)
  | .inr .headerSecond => readHeader (.inr .headerSecond) (.inl 0)
  | .inr .clearInput => MachineDrain.drain (.inr .input) (.inr .clearInput)
      (some (.inr .clockCopy))
  | .inr .clockCopy => Reduction.MachineTransfer.loopAt (.inl 2) (.inr .scratch)
      id false (.inr .clockCopy) (some (.inr .archiveCopy))
  | .inr .archiveCopy => Reduction.MachineTransfer.loopAt (.inr .archive) (.inr .scratch)
      id false (.inr .archiveCopy) (some (.inr .finalReverse))
  | .inr .finalReverse => Reduction.MachineTransfer.loopAt (.inr .scratch) (.inr .output)
      id false (.inr .finalReverse) none

def machine : FinTM2 where
  K := Tape
  k₀ := .inr .input
  k₁ := .inr .output
  Γ := Alphabet
  Λ := Label
  main := .inr .copyFirst
  σ := State
  initialState := initialState
  m := program

def clockTapes (tapes : Fin 3 → List Bool) (extra : ExtraTape → List Bool) : Tape → List Bool
  | .inl k => tapes k
  | .inr k => extra k

def clockConfiguration (extra : ExtraTape → List Bool) (register : Option Bool)
    (c : TM2.Cfg MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State) :
    TM2.Cfg Alphabet Label State := ⟨clockLabel c.l, (c.var, register), clockTapes c.stk extra⟩

theorem clockTapes_update (tapes : Fin 3 → List Bool) (extra : ExtraTape → List Bool)
    (k : Fin 3) (word : List Bool) :
    clockTapes (Function.update tapes k word) extra =
      Function.update (clockTapes tapes extra) (.inl k) word := by
  funext tape
  cases tape <;> simp [clockTapes, Function.comp_def]

theorem clockStatement_simulation (extra : ExtraTape → List Bool) (register : Option Bool)
    (statement : TM2.Stmt MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State)
    (state : MachineLogCounter.State) (tapes : Fin 3 → List Bool) :
    TM2.stepAux (clockStatement statement) (state, register) (clockTapes tapes extra) =
      clockConfiguration extra register (TM2.stepAux statement state tapes) := by
  induction statement generalizing state tapes with
  | push k f next ih =>
      simp only [clockStatement, TM2.stepAux, clockTapes]
      rw [← clockTapes_update]
      exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
      simpa only [clockStatement, TM2.stepAux, clockTapes] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      simp only [clockStatement, TM2.stepAux, clockTapes]
      rw [← clockTapes_update]
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
      simpa only [clockStatement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
      cases h : f state with
      | false => simpa only [clockStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [clockStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => rfl

theorem clockStep (extra : ExtraTape → List Bool) (register : Option Bool)
    (a b : MachineLogCounter.machine.Cfg)
    (h : MachineLogCounter.machine.step a = some b) :
    TM2.step program (clockConfiguration extra register a) =
      some (clockConfiguration extra register b) := by
  cases a with
  | mk label state tapes =>
      cases label with
      | none => cases h
      | some label =>
          have hb := Option.some.inj h
          subst b
          exact congrArg some (clockStatement_simulation extra register
            (MachineLogCounter.program label) state tapes)

def clockInTime (extra : ExtraTape → List Bool) (register : Option Bool) (n : Nat) :
    StateTransition.EvalsToInTime (TM2.step program)
      (clockConfiguration extra register (initList MachineLogCounter.machine (encodeWord n)))
      (some (clockConfiguration extra register
        (haltList MachineLogCounter.machine (encodeWord (n.log2 + 1))))) (8 * n + 4) :=
  MachineComposition.liftExecutionInTime _ _ (clockConfiguration extra register)
    (clockStep extra register) (MachineLogCounter.outputsInTime n)

end MaxCutGames.Foundations.Complexity.GraphCounterModel

/-! Actual archive-copy and unary-header addition before the embedded logarithm
machine. The two header values stay on tapes; they never enter finite control. -/

namespace MaxCutGames.Foundations.Complexity.GraphCounterModel

open Turing

def startExtra (input archive : List Bool) : ExtraTape → List Bool
  | .input => input
  | .archive => archive
  | _ => []

def startMemory (input archive sum : List Bool) : Tape → List Bool
  | .inl k => if k = 0 then sum else []
  | .inr k => startExtra input archive k

theorem startMemory_input_update (input archive sum replacement : List Bool) :
    Function.update (startMemory input archive sum) (.inr .input) replacement =
      startMemory replacement archive sum := by
  funext tape
  cases tape with
  | inl k => simp [startMemory]
  | inr k => cases k <;> simp [startMemory, startExtra]

theorem startMemory_sum_update (input archive sum replacement : List Bool) :
    Function.update (startMemory input archive sum) (.inl 0) replacement =
      startMemory input archive replacement := by
  funext tape
  cases tape with
  | inl k => by_cases h : k = 0 <;> simp [startMemory, h]
  | inr k => simp [startMemory]

theorem headerStep_zero (again next : Label)
    (atHeader : program again = readHeader again next)
    (suffix archive : List Bool) (sum : Nat)
    (state : MachineLogCounter.State) (register : Option Bool) :
    TM2.step program
      ⟨some again, (state, register), startMemory (encodeWord 0 ++ suffix) archive (encodeWord sum)⟩ =
      some ⟨some next, (state, none), startMemory suffix archive (encodeWord sum)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atHeader]
  simp only [readHeader, TM2.stepAux, startMemory, startExtra, encodeWord,
    List.replicate_zero, List.nil_append, List.singleton_append, List.head?_cons,
    List.tail_cons, Option.getD_some, Bool.cond_false]
  rw [startMemory_input_update]

theorem headerStep_succ (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    TM2.step program
      ⟨some again, (state, register),
        startMemory (encodeWord (n + 1) ++ suffix) archive (encodeWord sum)⟩ =
      some ⟨some again, (state, some true),
        startMemory (encodeWord n ++ suffix) archive (encodeWord (sum + 1))⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atHeader]
  simp only [readHeader, TM2.stepAux, startMemory, startExtra, encodeWord,
    List.replicate_succ, List.cons_append, List.head?_cons, List.tail_cons,
    Option.getD_some, Bool.cond_true]
  rw [startMemory_input_update, startMemory_sum_update]
  rfl

theorem headerTrace (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (state, register),
        startMemory (encodeWord n ++ suffix) archive (encodeWord sum)⟩) =
      some ⟨some next, (state, none), startMemory suffix archive (encodeWord (n + sum))⟩ := by
  induction n generalizing sum register with
  | zero =>
      simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some] using
        headerStep_zero again next atHeader suffix archive sum state register
  | succ n ih =>
      rw [Function.iterate_succ_apply, MachineComposition.advance_some]
      rw [headerStep_succ again next atHeader n sum suffix archive state register]
      simpa only [Nat.add_assoc, Nat.add_comm 1 sum] using ih (sum + 1) (some true)

def headerInTime (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (state, register), startMemory (encodeWord n ++ suffix) archive (encodeWord sum)⟩
      (some ⟨some next, (state, none), startMemory suffix archive (encodeWord (n + sum))⟩)
      (n + 1) where
  steps := n + 1
  evals_in_steps := headerTrace again next atHeader n sum suffix archive state register
  steps_le_m := le_rfl

theorem initialMemory (word : List Bool) :
    initList machine word =
      ⟨some (.inr .copyFirst), initialState, startMemory word [] []⟩ := by
  have ht : (initList machine word).stk = startMemory word [] [] := by
    funext tape
    cases tape with
    | inl k => simp [initList, machine, startMemory]
    | inr k =>
      cases k <;> simp [initList, machine, startMemory, startExtra]
      rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

theorem clockInitialMemory (word rest : List Bool) (sum : Nat) :
    clockConfiguration (startExtra rest word) none
      (initList MachineLogCounter.machine (encodeWord sum)) =
      ⟨some (.inl 0), initialState, startMemory rest word (encodeWord sum)⟩ := by
  have ht : clockTapes (initList MachineLogCounter.machine (encodeWord sum)).stk
      (startExtra rest word) = startMemory rest word (encodeWord sum) := by
    funext tape
    cases tape with
    | inl k => fin_cases k <;> rfl
    | inr k => rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

/-- Exact handoff from the genuine machine input to the actual logarithm
machine, with the original graph word protected in the archive. -/
def startInTime (n m : Nat) (rest : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (initList machine (encodeWords [n, m] ++ rest))
      (some (clockConfiguration (startExtra rest (encodeWords [n, m] ++ rest)) none
        (initList MachineLogCounter.machine (encodeWord (n + m)))))
      (2 * ((encodeWords [n, m] ++ rest).length + 1) + 1 + (n + 1) + (m + 1)) := by
  let word := encodeWords [n, m] ++ rest
  let b₀ := startMemory word [] []
  let b₁ := startMemory word word []
  let b₂ := startMemory word word (encodeWord 0)
  have hc : Function.update b₀ (.inr .archive) (b₀ (.inr .input) ++ b₀ (.inr .archive)) = b₁ := by
    funext tape
    cases tape with
    | inl k => simp [b₀, b₁, startMemory]
    | inr k => cases k <;> simp [b₀, b₁, startMemory, startExtra]
  let copy := MachineCopy.copyInTime (.inr ExtraTape.input) (.inr ExtraTape.archive)
    (.inr ExtraTape.scratch) (by decide) (by decide) (by decide) false
    (.inr ExtraLabel.copyFirst) (.inr ExtraLabel.copySecond) (some (.inr ExtraLabel.seed))
    program rfl rfl b₀ rfl MachineLogCounter.initialState none
  have copy' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .copyFirst), initialState, b₀⟩
      (some ⟨some (.inr .seed), initialState, b₁⟩) (2 * (word.length + 1)) := by
    have h := copy
    rw [hc] at h
    simpa only [initialState, show b₀ (.inr .input) = word from rfl] using h
  have seed : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .seed), initialState, b₁⟩
      (some ⟨some (.inr .headerFirst), initialState, b₂⟩) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change some (TM2.stepAux (program (.inr .seed)) initialState b₁) = _
    simp only [program, TM2.stepAux, b₁, startMemory]
    rw [startMemory_sum_update]
    rfl
  have first := headerInTime (.inr .headerFirst) (.inr .headerSecond) rfl
    n 0 (encodeWord m ++ rest) word MachineLogCounter.initialState none
  have first' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .headerFirst), initialState, b₂⟩
      (some ⟨some (.inr .headerSecond), initialState,
        startMemory (encodeWord m ++ rest) word (encodeWord n)⟩) (n + 1) := by
    simpa only [b₂, initialState, word, encodeWords, List.append_nil, List.append_assoc,
      Nat.add_zero] using first
  have second := headerInTime (.inr .headerSecond) (.inl 0) rfl
    m n rest word MachineLogCounter.initialState none
  have second' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .headerSecond), initialState,
        startMemory (encodeWord m ++ rest) word (encodeWord n)⟩
      (some ⟨some (.inl 0), initialState, startMemory rest word (encodeWord (n + m))⟩)
      (m + 1) := by simpa only [initialState, Nat.add_comm m n] using second
  let p₀ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ copy' seed
  let p₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀ first'
  let p := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₁ second'
  rw [initialMemory, clockInitialMemory]
  exact {
    toEvalsTo := p.toEvalsTo
    steps_le_m := by
      have h := p.steps_le_m
      change p.steps ≤ 2 * (word.length + 1) + 1 + (n + 1) + (m + 1)
      omega
  }

end MaxCutGames.Foundations.Complexity.GraphCounterModel

end OAI
