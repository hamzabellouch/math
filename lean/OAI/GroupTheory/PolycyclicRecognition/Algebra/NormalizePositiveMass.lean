import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

namespace OAI

/-! # Normalizing a positive partition mass bounded below by one -/

namespace PolycyclicRecognition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cutoff partition has mass at least one. Normalizing such vectors
costs at most a factor two in their normed distance. -/
theorem norm_normalized_sub_le_two (x y : E) (hx : 1 ≤ ‖x‖) (hy : 1 ≤ ‖y‖) :
    ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x - y‖ := by
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < ‖y‖ := lt_of_lt_of_le zero_lt_one hy
  have hcoef : (‖x‖⁻¹ - ‖y‖⁻¹) * ‖y‖ = (‖y‖ - ‖x‖) / ‖x‖ := by
    field_simp
  have he : ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ = |‖y‖ - ‖x‖| / ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ = |(‖x‖⁻¹ - ‖y‖⁻¹) * ‖y‖| := by
        rw [abs_mul, abs_of_nonneg (norm_nonneg y)]
      _ = |‖y‖ - ‖x‖| / ‖x‖ := by rw [hcoef, abs_div, abs_of_pos hx0]
  have hnorm : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by
    simpa only [dist_zero_right, dist_eq_norm, sub_zero, norm_sub_rev] using abs_dist_sub_le y x (0 : E)
  calc
    _ = ‖‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := by
      congr 1
      rw [smul_sub, sub_smul]
      abel
    _ ≤ ‖‖x‖⁻¹ • (x - y)‖ + ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := norm_add_le _ _
    _ = ‖x - y‖ / ‖x‖ + |‖y‖ - ‖x‖| / ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0), he]
      simp only [div_eq_inv_mul]
    _ ≤ ‖x - y‖ / ‖x‖ + ‖x - y‖ / ‖x‖ :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hnorm hx0.le)
    _ ≤ 2 * ‖x - y‖ := by
      have hdiv : ‖x - y‖ / ‖x‖ ≤ ‖x - y‖ :=
        (div_le_iff₀ hx0).mpr (by nlinarith only [hx, norm_nonneg (x - y)])
      linarith only [hdiv]

end PolycyclicRecognition

end OAI
