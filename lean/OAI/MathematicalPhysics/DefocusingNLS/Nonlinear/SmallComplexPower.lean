import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowParameterKernel
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace OAI

/-! # Uniform cancellation for bounded complex powers near one -/

namespace DefocusingNLS

theorem norm_log_mul_le_one_of_small (r z : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ‖r‖ ≤ M) (hz : ‖z‖ ≤ 1 / (2 * (M + 1))) :
    ‖z‖ ≤ 1 / 2 ∧ ‖Complex.log (1 + z) * r‖ ≤ 1 := by
  have hden : 0 < 2 * (M + 1) := by positivity
  have hs : ‖z‖ * (2 * (M + 1)) ≤ 1 := (le_div_iff₀ hden).mp hz
  have hzhalf : ‖z‖ ≤ 1 / 2 := by
    nlinarith [norm_nonneg z, mul_nonneg (norm_nonneg z) hM]
  refine ⟨hzhalf, ?_⟩
  rw [norm_mul]
  calc
    ‖Complex.log (1 + z)‖ * ‖r‖ ≤ ((3 / 2 : ℝ) * ‖z‖) * M := by
      gcongr
      exact Complex.norm_log_one_add_half_le_self hzhalf
    _ ≤ 1 := by nlinarith [norm_nonneg z]

theorem norm_cpow_sub_one_le_of_small (r z : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ‖r‖ ≤ M) (hz : ‖z‖ ≤ 1 / (2 * (M + 1))) :
    ‖(1 + z) ^ r - 1‖ ≤ 3 * M * ‖z‖ := by
  obtain ⟨hzhalf, harg⟩ := norm_log_mul_le_one_of_small r z M hM hr hz
  have hne : 1 + z ≠ 0 := by
    intro h
    have heq : z = -1 := by linear_combination h
    rw [heq, norm_neg, norm_one] at hzhalf
    norm_num at hzhalf
  rw [Complex.cpow_def_of_ne_zero hne]
  calc
    ‖Complex.exp (Complex.log (1 + z) * r) - 1‖ ≤
        2 * ‖Complex.log (1 + z) * r‖ := Complex.norm_exp_sub_one_le harg
    _ = 2 * (‖Complex.log (1 + z)‖ * ‖r‖) := by rw [norm_mul]
    _ ≤ 2 * (((3 / 2 : ℝ) * ‖z‖) * M) := by
      gcongr
      exact Complex.norm_log_one_add_half_le_self hzhalf
    _ = _ := by ring

theorem norm_log_mul_cpow_le_of_small (r z : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ‖r‖ ≤ M) (hz : ‖z‖ ≤ 1 / (2 * (M + 1))) :
    ‖Complex.log (1 + z) * (1 + z) ^ r‖ ≤
      ((3 / 2 : ℝ) * Real.exp 1) * ‖z‖ := by
  obtain ⟨hzhalf, harg⟩ := norm_log_mul_le_one_of_small r z M hM hr hz
  have hne : 1 + z ≠ 0 := by
    intro h
    have heq : z = -1 := by linear_combination h
    rw [heq, norm_neg, norm_one] at hzhalf
    norm_num at hzhalf
  have he : ‖(1 + z) ^ r‖ ≤ Real.exp 1 := by
    rw [Complex.cpow_def_of_ne_zero hne, Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans harg)
  rw [norm_mul]
  calc
    ‖Complex.log (1 + z)‖ * ‖(1 + z) ^ r‖ ≤
        ((3 / 2 : ℝ) * ‖z‖) * Real.exp 1 := by
      gcongr
      exact Complex.norm_log_one_add_half_le_self hzhalf
    _ = _ := by ring

end DefocusingNLS

end OAI
