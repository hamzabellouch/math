import Mathlib.Analysis.Complex.Basic
import OAI.NumberTheory.Ostmann.Preliminaries.Collision

namespace OAI

/-!
# Transfer from collision distance to test functions

The tests need only a bounded squared norm, not a pointwise bound. This is
the Cauchy--Schwarz estimate immediately following Lemma 2.5 in the paper.
-/

namespace Ostmann

open scoped BigOperators

theorem complex_weighted_sum_sq {α : Type*} (s : Finset α)
    (w : α → ℝ) (f : α → ℂ) :
    ‖∑ r ∈ s, (w r : ℂ) * f r‖ ^ 2 ≤
      (∑ r ∈ s, w r ^ 2) * ∑ r ∈ s, ‖f r‖ ^ 2 := by
  have hnorm : ‖∑ r ∈ s, (w r : ℂ) * f r‖ ≤ ∑ r ∈ s, |w r| * ‖f r‖ := by
    calc
      _ ≤ ∑ r ∈ s, ‖(w r : ℂ) * f r‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hnonneg : 0 ≤ ∑ r ∈ s, |w r| * ‖f r‖ :=
    Finset.sum_nonneg (fun r _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s (fun r => |w r|) (fun r => ‖f r‖)
  simp only [sq_abs] at hCS
  nlinarith [norm_nonneg (∑ r ∈ s, (w r : ℂ) * f r)]

/-- The empirical test error is bounded by the squared distance of the mass
function from the uniform mass on its support, times the test's energy. -/
theorem centered_test_bound {α : Type*} (s : Finset α) (μ : α → ℝ)
    (f : α → ℂ) (p : ℝ) (hf : (∑ r ∈ s, ‖f r‖ ^ 2) ≤ p) :
    ‖∑ r ∈ s, ((μ r - 1 / (s.card : ℝ) : ℝ) : ℂ) * f r‖ ^ 2 ≤
      p * ∑ r ∈ s, (μ r - 1 / (s.card : ℝ)) ^ 2 := by
  calc
    _ ≤ (∑ r ∈ s, (μ r - 1 / (s.card : ℝ)) ^ 2) * ∑ r ∈ s, ‖f r‖ ^ 2 :=
      complex_weighted_sum_sq s (fun r => μ r - 1 / (s.card : ℝ)) f
    _ ≤ (∑ r ∈ s, (μ r - 1 / (s.card : ℝ)) ^ 2) * p :=
      mul_le_mul_of_nonneg_left hf (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := mul_comm _ _

end Ostmann

end OAI
