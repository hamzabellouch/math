import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ClosedTailBounds
import OAI.Analysis.RieszRectifiability.Kernel.FarKernelDifference

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter

theorem inverseDistancePow_bound_of_separation {d : ℕ} (q : ℕ)
    (x y : Ambient d) (R : ℝ) (hR : 0 < R) (hsep : R ≤ dist x y) :
    inverseDistancePow q x y ≤ (R ^ q)⁻¹ := by
  simpa only [inverseDistancePow, one_div] using!
    one_div_le_one_div_of_le (pow_pos hR q) (pow_le_pow_left₀ hR.le hsep q)

theorem subtracted_far_test_kernel_uniform_bound {d : ℕ} (m : ℕ)
    (x y : Ambient d) (R : ℝ) (hR : 0 < R) (hx : R ≤ ‖x‖)
    (hy : y ∈ closedExterior x R) :
    |inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x| ≤
      2 * (R ^ (m + 1))⁻¹ := by
  have ha := inverseDistancePow_bound_of_separation (m + 1) x y R hR hy
  have hb := inverseDistancePow_bound_of_separation (m + 1) 0 x R hR
    (by simpa only [dist_zero_left] using! hx)
  have hna := inverseDistancePow_nonneg (m + 1) x y
  have hnb := inverseDistancePow_nonneg (m + 1) 0 x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem subtracted_far_test_kernel_central_bound {d : ℕ} (m : ℕ)
    (x y : Ambient d) (hx : 0 < ‖x‖) (hy : ‖y‖ ≤ ‖x‖ / 2) :
    |inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x| ≤
      (m + 1 : ℝ) * 2 ^ (m + 2) * ‖y‖ * inverseDistancePow (m + 2) 0 x := by
  have hh := inverseDistancePow_far_difference m (0 : Ambient d) y x
    (by simpa only [dist_zero_left] using! hx)
    (by simpa only [dist_zero_left, dist_zero_right] using! (show 2 * ‖y‖ ≤ ‖x‖ by linarith))
  simpa only [inverseDistancePow, dist_comm y x, dist_zero_right] using! hh

theorem subtracted_far_test_kernel_integrable {d : ℕ}
    (μ : Measure (Ambient d)) (g : Ambient d → ℂ) (hg : Integrable g μ)
    (m : ℕ) (x : Ambient d) (R : ℝ) (hR : 0 < R) (hx : R ≤ ‖x‖) :
    IntegrableOn (fun y => (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x) • g y)
      (closedExterior x R) μ := by
  apply hg.restrict.bdd_smul (2 * (R ^ (m + 1))⁻¹)
    (((inverseDistancePow_measurable (m + 1) x).sub measurable_const).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (closedExterior_measurable x R)] with y hy
  exact subtracted_far_test_kernel_uniform_bound m x y R hR hx hy

theorem raw_far_test_kernel_integrable {d : ℕ}
    (μ : Measure (Ambient d)) (g : Ambient d → ℂ) (hg : Integrable g μ)
    (m : ℕ) (x : Ambient d) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun y => inverseDistancePow (m + 1) x y • g y) (closedExterior x R) μ := by
  apply hg.restrict.bdd_smul ((R ^ (m + 1))⁻¹)
    (inverseDistancePow_measurable (m + 1) x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (closedExterior_measurable x R)] with y hy
  rw [Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
  exact inverseDistancePow_bound_of_separation (m + 1) x y R hR hy

end

end RieszRectifiability

end OAI
