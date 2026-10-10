import Mathlib
import OAI.Combinatorics.IndependentSets.Geometry.PatternInvariant
import OAI.Combinatorics.IndependentSets.Encoding.Target
import OAI.Combinatorics.IndependentSets.Machines.MachineComposition
import OAI.Combinatorics.IndependentSets.Machines.Placement

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineLogCounter

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

private theorem update_input (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 0 replacement = rawTapes replacement scratch output := by
  funext k
  fin_cases k <;> rfl

theorem update_scratch (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 1 replacement = rawTapes input replacement output := by
  funext k
  fin_cases k <;> rfl

theorem update_output (input scratch output replacement : List Bool) :
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
  rw [update_input, update_scratch]
  rfl

theorem stripStep_false (scratch output : List Bool) (state : State) :
    machine.step (configuration (some 1) state [false] scratch output) =
      some (configuration (some 4) initialState [] scratch output) := by
  change some (TM2.stepAux stripLoop state (rawTapes [false] scratch output)) = _
  simp [stripLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_input]
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
  rw [update_input]
  rfl

theorem halfStep_false (input scratch output : List Bool) (started : Bool) (register : Option Bool) :
    machine.step (configuration (some 3) ((false, started), register) (true :: input) scratch output) =
      some (configuration (some 3) ((true, started), some true) input scratch output) := by
  change some (TM2.stepAux halfLoop ((false, started), register)
    (rawTapes (true :: input) scratch output)) = _
  simp [halfLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_input]
  rfl

theorem halfStep_true (input scratch output : List Bool) (started : Bool) (register : Option Bool) :
    machine.step (configuration (some 3) ((true, started), register) (true :: input) scratch output) =
      some (configuration (some 3) ((false, started), some true) input (true :: scratch) output) := by
  change some (TM2.stepAux halfLoop ((true, started), register)
    (rawTapes (true :: input) scratch output)) = _
  simp [halfLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_input, update_scratch]
  rfl

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
  · rw [update_output]
    rfl
  · rfl

theorem guardStep_positive (n : Nat) (output : List Bool) (started : Bool) :
    machine.step (configuration (some 2) ((false, started), none)
      (List.replicate (n + 1) true) [] output) =
      some (configuration (some 3) ((false, true), none)
        (List.replicate (n + 1) true) [] (true :: output)) := by
  change some (TM2.stepAux guardLoop ((false, started), none)
    (rawTapes (true :: List.replicate n true) [] output)) = _
  simp [guardLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_output]
  simp only [List.replicate_succ]
  rfl

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
      | false =>
        simp [increments, next]
        exact guardStep_zero output false
      | true =>
        simp [increments, next]
        exact guardStep_zero output true
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
  rw [update_output]
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

end IndependentSetsGames.Foundations.Complexity.MachineLogCounter

end OAI
