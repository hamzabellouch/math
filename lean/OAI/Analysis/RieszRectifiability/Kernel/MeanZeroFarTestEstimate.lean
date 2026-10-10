import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.SubtractedFarTestEstimate

namespace OAI

/-!
# Mean-zero decay of the far test integral

Subtracting the kernel value at the origin exposes a first-moment bound.
The mean-zero hypothesis replaces the remaining far-region integral by its
complement, whose distance from the origin gives the same extra decay power.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set

theorem mean_zero_far_test_integral_bound {d : ℕ}
    (μ : Measure (Ambient d)) (g : Ambient d → ℂ) (hg : Integrable g μ)
    (hm : Integrable (fun y => ‖y‖ * ‖g y‖) μ) (hmean : (∫ y, g y ∂μ) = 0)
    (m : ℕ) (x : Ambient d) (hx : 0 < ‖x‖) :
    ‖∫ y in closedExterior x (‖x‖ / 2), inverseDistancePow (m + 1) x y • g y ∂μ‖ ≤
      (((m + 1 : ℝ) * 2 ^ (m + 2) + 2 ^ (m + 3) + 2) *
        (∫ y, ‖y‖ * ‖g y‖ ∂μ)) / ‖x‖ ^ (m + 2) := by
  let R := ‖x‖ / 2
  let E := closedExterior x R
  let K := inverseDistancePow (m + 1) 0 x
  let F := fun y => (inverseDistancePow (m + 1) x y - K) • g y
  let M := ∫ y, ‖y‖ * ‖g y‖ ∂μ
  have hR : 0 < R := by dsimp [R]; positivity
  have hE : MeasurableSet E := closedExterior_measurable x R
  have hK : 0 ≤ K := inverseDistancePow_nonneg _ _ _
  have hF : IntegrableOn F E μ := subtracted_far_test_kernel_integrable μ g hg m x R hR
    (by dsimp [R]; linarith)
  have hmissing : (∫ y in Eᶜ, ‖g y‖ ∂μ) ≤ M / R := by
    apply first_absolute_moment_bound_on_set μ g hg hm Eᶜ hE.compl R hR
    intro y hy
    have hd : dist x y < R := by
      simpa only [E, closedExterior, mem_compl_iff, mem_ofPred_eq, not_le] using! hy
    have hn := norm_sub_norm_le x y
    rw [← dist_eq_norm] at hn
    dsimp [R] at hd ⊢
    linarith
  have hmeanE : (∫ y in E, g y ∂μ) = -(∫ y in Eᶜ, g y ∂μ) := by
    apply eq_neg_iff_add_eq_zero.mpr
    exact (integral_add_compl hE hg).trans hmean
  have hdecomp : (∫ y in E, inverseDistancePow (m + 1) x y • g y ∂μ) =
      (∫ y in E, F y ∂μ) + K • (∫ y in E, g y ∂μ) := by
    have heq : (fun y => inverseDistancePow (m + 1) x y • g y) = fun y => F y + K • g y := by
      funext y
      dsimp only [F]
      simp only [RCLike.real_smul_eq_coe_mul, map_sub]
      ring
    have hKg : IntegrableOn (fun y => K • g y) E μ := hg.restrict.smul K
    rw [heq, integral_add hF hKg]
    congr 1
    exact integral_smul K g
  have hsub := (norm_integral_le_integral_norm (μ := μ.restrict E) F).trans
    (subtracted_far_test_integral_norm_bound μ g hg hm m x hx)
  have hcorrection : ‖K • (-(∫ y in Eᶜ, g y ∂μ))‖ ≤ K * (M / R) := by
    rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg hK, norm_neg]
    exact mul_le_mul_of_nonneg_left
      ((norm_integral_le_integral_norm (μ := μ.restrict Eᶜ) g).trans hmissing) hK
  rw [hdecomp, hmeanE]
  calc
    _ ≤ ‖∫ y in E, F y ∂μ‖ + ‖K • (-(∫ y in Eᶜ, g y ∂μ))‖ := norm_add_le _ _
    _ ≤ (((m + 1 : ℝ) * 2 ^ (m + 2) + 2 ^ (m + 3)) * M) / ‖x‖ ^ (m + 2) + K * (M / R) :=
      add_le_add hsub hcorrection
    _ = _ := by
      dsimp [K, R, M]
      simp only [inverseDistancePow, dist_zero_left, pow_add]
      field_simp

end

end RieszRectifiability

end OAI
