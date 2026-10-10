import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.FarTestKernelBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter

theorem kernel_test_integrable_from_separated_support {d : ℕ}
    (ν : Measure (Ambient d)) (g : Ambient d → ℂ) (hgm : Measurable g) (hg : Integrable g ν)
    (m : ℕ) (y : Ambient d) (R : ℝ) (hR : 0 < R)
    (hsep : ∀ᵐ x ∂ν, g x ≠ 0 → R ≤ dist x y) :
    Integrable (fun x => inverseDistancePow (m + 1) x y • g x) ν := by
  have hm : Measurable (fun x => inverseDistancePow (m + 1) x y • g x) := by
    unfold inverseDistancePow
    simp_rw [Complex.real_smul]
    fun_prop
  apply (hg.norm.const_mul ((R ^ (m + 1))⁻¹)).mono' hm.aestronglyMeasurable
  filter_upwards [hsep] with x hx
  by_cases hgx : g x = 0
  · rw [hgx]
    simp
  · rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal,
      abs_of_nonneg (inverseDistancePow_nonneg _ _ _)]
    exact mul_le_mul_of_nonneg_right
      (inverseDistancePow_bound_of_separation (m + 1) x y R hR (hx hgx)) (norm_nonneg _)

theorem far_kernel_test_integrable_of_support {d : ℕ}
    (ν : Measure (Ambient d)) (g : Ambient d → ℂ) (hgm : Measurable g) (hg : Integrable g ν)
    (m : ℕ) (a y : Ambient d) (H R : ℝ) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hnear : ∀ᵐ x ∂ν, g x ≠ 0 → dist x a ≤ H) (hfar : R ≤ dist a y) :
    Integrable (fun x => inverseDistancePow (m + 1) x y • g x) ν := by
  have hy : 0 < dist a y := hR.trans_le hfar
  apply kernel_test_integrable_from_separated_support ν g hgm hg m y (dist a y / 2) (by positivity)
  filter_upwards [hnear] with x hx
  intro hgx
  have ht := dist_triangle a x y
  rw [dist_comm a x] at ht
  linarith [hx hgx]

end

end RieszRectifiability

end OAI
