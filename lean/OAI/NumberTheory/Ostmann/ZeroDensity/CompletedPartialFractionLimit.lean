import OAI.NumberTheory.Ostmann.ZeroDensity.CompletedFiniteLogDerivative
import OAI.NumberTheory.Ostmann.ZeroDensity.CompletedQuotientGrowth
import OAI.NumberTheory.Ostmann.ZeroDensity.LogarithmicDiskRate

namespace OAI

/-! # The limit of actual completed-L logarithmic-derivative differences -/

namespace Ostmann

open Complex Filter Metric Set
open scoped Topology

/-- Subtracting at two fixed nonzero points cancels the constant logarithmic
part. This is the exact part of Hadamard factorization needed below. -/
theorem completed_partial_fraction_difference_tendsto (χ : PrimitiveComplexCharacter)
    (x y : ℂ) (hx : χ.completed x ≠ 0) (hy : χ.completed y ≠ 0) :
    Tendsto (fun n : ℕ => completedZeroPartialFraction χ ((n : ℝ) + 1) y -
      completedZeroPartialFraction χ ((n : ℝ) + 1) x) atTop
      (𝓝 (logDeriv χ.completed y - logDeriv χ.completed x)) := by
  obtain ⟨C, hC, hgrowth⟩ := completed_quotient_log_growth χ
  let D : ℝ := |Real.log ‖χ.completed 0‖| + 1
  let A : ℕ → ℝ := fun n => C * ((n : ℝ) + 9) * (1 + Real.log ((n : ℝ) + 9)) + D
  have hA (n : ℕ) : 0 < A n := by
    have hl : 0 ≤ Real.log ((n : ℝ) + 9) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
    dsimp [A, D]
    positivity
  have hlim : Tendsto (fun n : ℕ =>
      (64 * A n / (2 * ((n : ℝ) + 1)) ^ 2) * ‖y - x‖) atTop (𝓝 0) := by
    have hh := (logarithmic_disk_rate C 9 D (by norm_num)).const_mul (16 * ‖y - x‖)
    simp only [mul_zero] at hh
    convert hh using 1
    funext n
    dsimp [A]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn]
    ring
  have hlarge := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * (‖x‖ + ‖y‖) + 1)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hlim
  filter_upwards [hlarge] with n hn
  obtain ⟨g, hg, he, hne, hl⟩ := hgrowth n
  have hxsize : ‖x‖ ≤ (2 * ((n : ℝ) + 1)) / 4 := by linarith [norm_nonneg y]
  have hysize : ‖y‖ ≤ (2 * ((n : ℝ) + 1)) / 4 := by linarith [norm_nonneg x]
  have hh := logDeriv_disk_oscillation g (2 * ((n : ℝ) + 1)) (A n)
    (by positivity) (hA n) (fun z _ => hg z)
    (fun z hz => hne z (ball_subset_closedBall hz))
    (by simpa only [A, D, add_assoc] using hl) x y hxsize hysize
  have hx' := completed_logDeriv_remove_finite χ ((n : ℝ) + 1) g hg he x hx
  have hy' := completed_logDeriv_remove_finite χ ((n : ℝ) + 1) g hg he y hy
  have herr : (completedZeroPartialFraction χ ((n : ℝ) + 1) y -
      completedZeroPartialFraction χ ((n : ℝ) + 1) x) -
      (logDeriv χ.completed y - logDeriv χ.completed x) =
        -(logDeriv g y - logDeriv g x) := by
    rw [← hx', ← hy']
    ring
  rw [herr, norm_neg]
  exact hh

end Ostmann

end OAI
