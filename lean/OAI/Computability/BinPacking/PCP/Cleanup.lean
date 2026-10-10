import Mathlib.Algebra.BigOperators.Fin
import OAI.Computability.BinPacking.Computation.MachineUnaryLessAt

namespace OAI

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Cleanup

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

end BinPackingGames.Foundations.PCP.AlphabetTable.Cleanup

end OAI
