import OAI.Combinatorics.ContingencyTables.Rooted.RootedStoredEstimate
import Mathlib.Data.List.GetD

namespace OAI

/-! # Stored rational outputs of the actual outer phases

The initial record is at index zero. Later records are the outputs
stored in the finite history; the initial record also supplies every
unused future entry to the restart's multiplier function.
-/

namespace ContingencyTables.RootedStoredHistory

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionPhaseWords (Stored)
open RootedStoredEstimate RootedPhaseTrial
open CompanionTerminalMass (Endpoints tableCount)
open CompanionTerminalApplication (finalPhase)
open TwoLiftStates
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def lookup (A : Instance I J) (history : List (Stored A)) : ℕ → Stored A
  | 0 => initialStored A
  | i+1 => history.getD i (initialStored A)

lemma lookup_snoc_old (A : Instance I J) (history : List (Stored A))
    (next : Stored A) (i : ℕ) (hi : i ≤ history.length) :
    lookup A (history++[next]) i=lookup A history i := by
  cases i with
  | zero => rfl
  | succ i => exact List.getD_append history [next] (initialStored A) i (by omega)

lemma lookup_snoc_new (A : Instance I J) (history : List (Stored A)) (next : Stored A) :
    lookup A (history++[next]) (history.length+1)=next := by
  simp only [lookup,List.getD_append_right history [next] (initialStored A) history.length le_rfl,
    Nat.sub_self,List.getD_cons_zero]

lemma lookup_future (A : Instance I J) (history : List (Stored A)) (i : ℕ)
    (hi : history.length < i) : lookup A history i=initialStored A := by
  cases i with
  | zero => omega
  | succ i => exact List.getD_eq_default history (initialStored A) (by omega)

def Good (A : Instance I J) (R : RootedCompletion.Selection A.T) (xi : ℚ) (eta : ℝ)
    (history : List (Stored A)) : Prop :=
  ∀ i,i < history.length →
    ValidOutput A R i (lookup A history i) xi eta (lookup A history (i+1))

lemma good_nil (A : Instance I J) (R : RootedCompletion.Selection A.T) (xi : ℚ) (eta : ℝ) :
    Good A R xi eta [] := by
  intro i hi
  simp at hi

lemma good_snoc (A : Instance I J) (R : RootedCompletion.Selection A.T) (xi : ℚ) (eta : ℝ)
    (history : List (Stored A)) (next : Stored A) :
    Good A R xi eta (history++[next]) ↔
      Good A R xi eta history ∧
        ValidOutput A R history.length (lookup A history history.length) xi eta next := by
  constructor
  · intro h
    constructor
    · intro i hi
      have hstep := h i (by simp; omega)
      rw [lookup_snoc_old A history next i (by omega),
        lookup_snoc_old A history next (i+1) (by omega)] at hstep
      exact hstep
    · have hstep := h history.length (by simp)
      rw [lookup_snoc_old A history next history.length le_rfl,
        lookup_snoc_new] at hstep
      exact hstep
  · rintro ⟨hold,hnext⟩ i hi
    have hi' : i ≤ history.length := by simpa using Nat.le_of_lt_succ (by simpa using hi)
    by_cases heq : i=history.length
    · subst i
      rw [lookup_snoc_old A history next history.length le_rfl,lookup_snoc_new]
      exact hnext
    · have hlt : i < history.length := by omega
      rw [lookup_snoc_old A history next i hi',
        lookup_snoc_old A history next (i+1) (by omega)]
      exact hold i hlt

lemma good_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (xi : ℚ) (eta : ℝ)
    (history : List (Stored A)) (hg : Good A R xi eta history) (i : ℕ) :
    (∀ p q,0 < (lookup A history i).multiplier p q) ∧
      0 < (lookup A history i).estimate := by
  by_cases hi : i ≤ history.length
  · cases i with
    | zero => exact initialStored_positive A R
    | succ i =>
      have h := hg i (by omega)
      exact ⟨h.1,h.2.1⟩
  · rw [lookup_future A history i (by omega)]
    exact initialStored_positive A R

lemma good_multipliers (A : Instance I J) (R : RootedCompletion.Selection A.T) (xi : ℚ) (eta : ℝ)
    (history : List (Stored A)) (hg : Good A R xi eta history) (i : ℕ)
    (hi : i ≤ history.length) :
    GoodMultipliers pairs (RootedAnnealing.weight A R i)
      (fun p q => ((lookup A history i).multiplier p q:ℝ)) := by
  cases i with
  | zero => exact initialStored_good A R
  | succ i => exact (hg i (by omega)).2.2.1

/-- The rational value actually stored at the terminal history index
has the counting guarantee whenever every executed update is valid. -/
theorem count_accuracy (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (E : Endpoints A) (L : ℕ) (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (hW : 20*A.d ≤ A.W) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^L)
    (xi : ℚ) (eta : ℝ)
    (herr : (finalPhase A L epsilon:ℝ)*(4*(xi:ℝ)+4*eta) ≤ epsilon/50)
    (history : List (Stored A)) (hlen : history.length=finalPhase A L epsilon)
    (hg : Good A R xi eta history) :
    (1-epsilon)*tableCount A ≤ ((lookup A history history.length).estimate:ℝ) ∧
      ((lookup A history history.length).estimate:ℝ) ≤ (1+epsilon)*tableCount A := by
  rw [hlen]
  exact stored_count_accuracy A R E L epsilon he0 he1 hW hL (lookup A history) rfl xi eta
    herr (fun j hj => hg j (by simpa only [hlen] using hj))

end
end ContingencyTables.RootedStoredHistory

end OAI
