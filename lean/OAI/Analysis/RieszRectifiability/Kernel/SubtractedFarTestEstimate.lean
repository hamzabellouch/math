import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.SchwartzFirstMomentTails
import OAI.Analysis.RieszRectifiability.Kernel.FarTestKernelBounds

namespace OAI

/-!
# First-moment control of the subtracted far test

The far-region integral splits at the ball of radius `‖x‖ / 2` about the origin.
The central part uses the kernel difference estimate, while the outer part uses
the first absolute moment to gain the same decay of order `‖x‖ ^ (m + 2)`.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set

theorem subtracted_far_test_integral_norm_bound {d : ℕ}
    (μ : Measure (Ambient d)) (g : Ambient d → ℂ) (hg : Integrable g μ)
    (hm : Integrable (fun y => ‖y‖ * ‖g y‖) μ) (m : ℕ)
    (x : Ambient d) (hx : 0 < ‖x‖) :
    (∫ y in closedExterior x (‖x‖ / 2),
      ‖(inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x) • g y‖ ∂μ) ≤
      (((m + 1 : ℝ) * 2 ^ (m + 2) + 2 ^ (m + 3)) *
        (∫ y, ‖y‖ * ‖g y‖ ∂μ)) / ‖x‖ ^ (m + 2) := by
  let R := ‖x‖ / 2
  let E := closedExterior x R
  let B := closedBall (0 : Ambient d) R
  let F := fun y => (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x) • g y
  let M := ∫ y, ‖y‖ * ‖g y‖ ∂μ
  let D := (m + 1 : ℝ) * 2 ^ (m + 2) * inverseDistancePow (m + 2) 0 x
  let A := 2 * (R ^ (m + 1))⁻¹
  have hR : 0 < R := by dsimp [R]; positivity
  have hxR : R ≤ ‖x‖ := by dsimp [R]; linarith
  have hD : 0 ≤ D := mul_nonneg (by positivity) (inverseDistancePow_nonneg _ _ _)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hF : IntegrableOn F E μ := subtracted_far_test_kernel_integrable μ g hg m x R hR hxR
  have hcentral : (∫ y in E ∩ B, ‖F y‖ ∂μ) ≤ D * M := by
    have hf : IntegrableOn (fun y => ‖F y‖) (E ∩ B) μ :=
      hF.norm.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
    have hmi := hm.restrict (s := E ∩ B)
    calc
      _ ≤ ∫ y in E ∩ B, D * (‖y‖ * ‖g y‖) ∂μ := by
        apply integral_mono_ae hf (hmi.const_mul D)
        filter_upwards [ae_restrict_mem ((closedExterior_measurable x R).inter measurableSet_closedBall)] with y hy
        have hyR : ‖y‖ ≤ ‖x‖ / 2 := by simpa only [B, mem_closedBall, dist_zero_right] using! hy.2
        have hb := subtracted_far_test_kernel_central_bound m x y hx hyR
        change ‖(inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x) • g y‖ ≤ _
        rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
        calc
          _ ≤ ((m + 1 : ℝ) * 2 ^ (m + 2) * ‖y‖ * inverseDistancePow (m + 2) 0 x) * ‖g y‖ :=
            mul_le_mul_of_nonneg_right hb (norm_nonneg _)
          _ = _ := by dsimp [D]; ring
      _ = D * (∫ y in E ∩ B, ‖y‖ * ‖g y‖ ∂μ) := integral_const_mul _ _
      _ ≤ D * M := mul_le_mul_of_nonneg_left
        (integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall fun y => mul_nonneg (norm_nonneg y) (norm_nonneg (g y))) hm) hD
  have houter : (∫ y in E \ B, ‖F y‖ ∂μ) ≤ A * (M / R) := by
    have hf : IntegrableOn (fun y => ‖F y‖) (E \ B) μ :=
      hF.norm.mono_measure (Measure.restrict_mono sdiff_subset le_rfl)
    have hsep : ∀ y ∈ E \ B, R ≤ ‖y‖ := by
      intro y hy
      exact (lt_of_not_ge (by simpa only [B, mem_closedBall, dist_zero_right] using! hy.2)).le
    have ht := first_absolute_moment_bound_on_set μ g hg hm (E \ B)
      ((closedExterior_measurable x R).diff measurableSet_closedBall) R hR hsep
    calc
      _ ≤ ∫ y in E \ B, A * ‖g y‖ ∂μ := by
        apply integral_mono_ae hf (hg.norm.restrict.const_mul A)
        filter_upwards [ae_restrict_mem ((closedExterior_measurable x R).diff measurableSet_closedBall)] with y hy
        change ‖(inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x) • g y‖ ≤ _
        rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
        exact mul_le_mul_of_nonneg_right (subtracted_far_test_kernel_uniform_bound m x y R hR hxR hy.1)
          (norm_nonneg _)
      _ = A * (∫ y in E \ B, ‖g y‖ ∂μ) := integral_const_mul _ _
      _ ≤ A * (M / R) := mul_le_mul_of_nonneg_left ht hA
  calc
    _ = (∫ y in E ∩ B, ‖F y‖ ∂μ) + ∫ y in E \ B, ‖F y‖ ∂μ :=
      (integral_inter_add_sdiff measurableSet_closedBall hF.norm).symm
    _ ≤ D * M + A * (M / R) := add_le_add hcentral houter
    _ = _ := by
      dsimp [D, A, R, M]
      simp only [inverseDistancePow, dist_zero_left, pow_add, div_pow]
      field_simp

end

end RieszRectifiability

end OAI
