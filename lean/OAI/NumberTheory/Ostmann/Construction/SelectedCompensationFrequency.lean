import OAI.NumberTheory.Ostmann.Construction.SelectedCompensationPrior
import OAI.NumberTheory.Ostmann.Arithmetic.MovingProductRounding

namespace OAI

/-! # The selected compensation list supplies the actual frequency-budget data -/
namespace Ostmann
open scoped Classical BigOperators

private theorem headD_drop_get {α : Type*} (xs : List α) (fallback : α)
    (n : ℕ) (hn : n < xs.length) :
    (xs.drop n).headD fallback = xs.get ⟨n, hn⟩ := by
  induction xs generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simpa only [List.drop_succ_cons, List.get_cons_succ] using ih n (by simpa using hn)

theorem selectedCompensation_pivot_error
    {A B : Set ℕ} {N hi : ℕ} {a C L X : ℝ} {D : Finset ℕ}
    {centers : List ℕ} {targets : List ℝ}
    (h : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) centers targets)
    (n : ℕ) (hn : n < targets.length)
    (G : ℝ) :
    |movingCellPivotExponent (fun _ => G) (selectedCompensationCenter centers) n -
      movingTargetPivotExponent G targets n| ≤
        (2 : ℝ) ^ n * (256 * tailDefectBudget a C X + 9) := by
  have hnc : n < centers.length := by rw [h.length_eq]; exact hn
  have hc := h.get hnc hn
  rw [← headD_drop_get centers 0 n hnc, ← headD_drop_get targets 0 n hn] at hc
  have hlo := hc.1
  have hhi := hc.2.1
  have hD : 0 ≤ 64 * tailDefectBudget a C X + 1 := by linarith
  have hr : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hr0 : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hlow := mul_le_mul_of_nonneg_left hlo hr0
  have hupp := mul_le_mul_of_nonneg_left hhi hr0
  have hbudget := mul_le_mul_of_nonneg_left hD hr0
  simp only [movingCellPivotExponent, selectedCompensationCenter, movingTargetPivotExponent,
    add_sub_cancel_right, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact abs_le.mpr ⟨by nlinarith only [hlow, hbudget, hr], by nlinarith only [hupp, hr]⟩

theorem selectedCompensation_index_data
    {A B : Set ℕ} {N hi : ℕ} {a C L X : ℝ} {D P : Finset ℕ}
    {centers : List ℕ} {targets : List ℝ}
    (h : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) centers targets)
    (n : ℕ) (hn : n < targets.length)
    (hsub : selectedTailCellPrimes A B N X hi D ((centers.drop n).headD 0) ⊆ P)
    (G : ℝ) :
    (∑ q : P, selectedCompensationPrior A B N X hi D P centers n q) = 1 ∧
      (∀ q : P, (q : ℝ) * selectedCompensationPrior A B N X hi D P centers n q ≤ Real.exp (2 * L)) ∧
      |movingCellPivotExponent (fun _ => G) (selectedCompensationCenter centers) n -
        movingTargetPivotExponent G targets n| ≤
          (2 : ℝ) ^ n * (256 * tailDefectBudget a C X + 9) := by
  have hnc : n < centers.length := by rw [h.length_eq]; exact hn
  have hc := h.get hnc hn
  rw [← headD_drop_get centers 0 n hnc, ← headD_drop_get targets 0 n hn] at hc
  have hp := selectedCompensationPrior_properties hc hsub
  refine ⟨hp.1, hp.2.1, ?_⟩
  exact selectedCompensation_pivot_error h n hn G

end Ostmann

end OAI
