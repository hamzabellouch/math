import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

namespace OAI

/-! Symmetric double and quadruple sums over unordered pairs. -/

section

noncomputable section
open scoped BigOperators Classical
namespace Paper170

def upperPairSum {α : Type*} [Fintype α] [LinearOrder α] (f : α → α → ℝ) : ℝ :=
  ∑ i, ∑ p, if i < p then f i p else 0

theorem upperPairSum_mul {α : Type*} [Fintype α] [LinearOrder α]
    (r : ℝ) (f : α → α → ℝ) :
    upperPairSum (fun i p => r * f i p) = r * upperPairSum f := by
  simp only [upperPairSum, Finset.mul_sum, mul_ite, mul_zero]

theorem sum_symmetric_pair {α : Type*} [Fintype α] [LinearOrder α]
    (f : α → α → ℝ) (hsym : ∀ i p, f p i = f i p) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ p, f i p) = 2 * upperPairSum f := by
  have hpoint (i p : α) : f i p =
      (if i < p then f i p else 0) + (if p < i then f i p else 0) := by
    rcases lt_trichotomy i p with h | rfl | h
    · simp [h, not_lt_of_ge h.le]
    · simp [hdiag]
    · simp [h, not_lt_of_ge h.le]
  have hsum : (∑ i, ∑ p, f i p) =
      upperPairSum f + ∑ i, ∑ p, if p < i then f i p else 0 := by
    calc
      _ = ∑ i, ∑ p, ((if i < p then f i p else 0) +
          (if p < i then f i p else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro p _
        exact hpoint i p
      _ = _ := by simp only [upperPairSum, Finset.sum_add_distrib]
  rw [hsum, Finset.sum_comm]
  have he : (∑ p, ∑ i, if p < i then f i p else 0) = upperPairSum f := by
    unfold upperPairSum
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro i _
    rw [hsym]
  rw [he]
  ring

theorem sum_symmetric_quad {α : Type*} [Fintype α] [LinearOrder α]
    (f : α → α → α → α → ℝ)
    (hfirst : ∀ i p k q, f p i k q = f i p k q)
    (hsecond : ∀ i p k q, f i p q k = f i p k q)
    (hdiag₁ : ∀ i k q, f i i k q = 0) (hdiag₂ : ∀ i p k, f i p k k = 0) :
    (∑ i, ∑ p, ∑ k, ∑ q, f i p k q) =
      4 * upperPairSum (fun i p => upperPairSum (f i p)) := by
  have hs (i p : α) : (∑ k, ∑ q, f p i k q) = ∑ k, ∑ q, f i p k q := by
    simp only [hfirst]
  have hd (i : α) : (∑ k, ∑ q, f i i k q) = 0 := by simp [hdiag₁]
  rw [sum_symmetric_pair _ hs hd]
  have he : (fun i p => ∑ k, ∑ q, f i p k q) =
      (fun i p => 2 * upperPairSum (f i p)) := by
    funext i p
    exact sum_symmetric_pair _ (hsecond i p) (hdiag₂ i p)
  rw [he, upperPairSum_mul]
  ring

end Paper170

end
end

end OAI
