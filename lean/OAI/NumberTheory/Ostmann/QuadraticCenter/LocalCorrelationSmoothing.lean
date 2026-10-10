import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem finite_abel_identity (a w : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, a n * w n) =
      (∑ n ∈ Finset.range N, a n) * w N +
        ∑ n ∈ Finset.range N, (∑ k ∈ Finset.range (n + 1), a k) * (w n - w (n + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Finset.sum_range_succ]
    ring

theorem finite_abel_norm_bound (a w : ℕ → ℂ) (N : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hpartial : ∀ M ≤ N, ‖∑ n ∈ Finset.range M, a n‖ ≤ B) :
    ‖∑ n ∈ Finset.range N, a n * w n‖ ≤
      B * (‖w N‖ + ∑ n ∈ Finset.range N, ‖w n - w (n + 1)‖) := by
  rw [finite_abel_identity]
  calc
    _ ≤ ‖(∑ n ∈ Finset.range N, a n) * w N‖ +
        ‖∑ n ∈ Finset.range N,
          (∑ k ∈ Finset.range (n + 1), a k) * (w n - w (n + 1))‖ := norm_add_le _ _
    _ ≤ B * ‖w N‖ + ∑ n ∈ Finset.range N, B * ‖w n - w (n + 1)‖ := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul (hpartial N le_rfl) le_rfl (norm_nonneg _) hB
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hpartial (n + 1) (Finset.mem_range.mp hn))
          (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem sampled_variation_le_integral (w dw : ℝ → ℂ) (hdw : Continuous dw)
    (hderiv : ∀ x, HasDerivAt w (dw x) x) (a : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, ‖w (a + n) - w (a + (n + 1 : ℕ))‖) ≤
      ∫ x in a..(a + N), ‖dw x‖ := by
  have hpoint (n : ℕ) : ‖w (a + n) - w (a + (n + 1 : ℕ))‖ ≤
      ∫ x in (a + n)..(a + (n + 1 : ℕ)), ‖dw x‖ := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x) (hdw.intervalIntegrable (a + n) (a + (n + 1 : ℕ)))
    rw [norm_sub_rev, ← hi]
    exact intervalIntegral.norm_integral_le_integral_norm (by simp)
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        ∫ x in (a + n)..(a + (n + 1 : ℕ)), ‖dw x‖ :=
      Finset.sum_le_sum (fun n _ => hpoint n)
    _ = _ := by
      simpa only [Nat.cast_zero, add_zero] using
        intervalIntegral.sum_integral_adjacent_intervals
          (a := fun n : ℕ => a + n) (n := N)
          (fun n _ => hdw.norm.intervalIntegrable _ _)

theorem smooth_weighted_sum_bound (a : ℕ → ℂ) (w dw : ℝ → ℂ)
    (hdw : Continuous dw) (hderiv : ∀ x, HasDerivAt w (dw x) x)
    (start : ℝ) (N : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hpartial : ∀ M ≤ N, ‖∑ n ∈ Finset.range M, a n‖ ≤ B) :
    ‖∑ n ∈ Finset.range N, a n * w (start + n)‖ ≤
      B * (‖w (start + N)‖ + ∫ x in start..(start + N), ‖dw x‖) := by
  have h := finite_abel_norm_bound a (fun n => w (start + n)) N hB hpartial
  exact h.trans (mul_le_mul_of_nonneg_left
    (add_le_add_right (sampled_variation_le_integral w dw hdw hderiv start N) _) hB)

end Ostmann.QuadraticCenter

end

end OAI
