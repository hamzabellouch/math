import OAI.MeasureTheory.Falconer.Shells.SpatialSharedShell

namespace OAI

/-! # Boundedness and shell integrability of the shared spatial amplitude -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem spatialSharedAmplitude_norm_le
    (c : Space d → ℂ) (hc : Integrable c)
    (U V : Space d × (ℝ × Sphere d) → ℂ)
    {B C : ℝ} (hB : 0 ≤ B)
    (hbU : ∀ z, ‖U z‖ ≤ B) (hbV : ∀ z, ‖V z‖ ≤ C) (r : ℝ) :
    ‖spatialSharedAmplitude c U V r‖ ≤
      ((∫ ξ : Space d, ‖c ξ‖)*(B*C))*(sphereMeasure d).real univ := by
  apply norm_integral_le_of_norm_le_const
  apply Filter.Eventually.of_forall
  intro w
  calc
    _ ≤ ∫ ξ : Space d, ‖c ξ‖*(B*C) := by
      apply norm_integral_le_of_norm_le (hc.norm.mul_const (B*C))
      apply Filter.Eventually.of_forall
      intro ξ
      rw [norm_mul,norm_mul,norm_star]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hbU (ξ,(r,w))) (hbV (ξ,(r,w))) (norm_nonneg _) hB)
        (norm_nonneg _)
    _ = _ := integral_mul_const _ _

theorem spatialSharedAmplitude_sq_integrable
    (c : Space d → ℂ) (hcm : Measurable c) (hc : Integrable c)
    (U V : Space d × (ℝ × Sphere d) → ℂ)
    (hU : Measurable U) (hV : Measurable V)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbU : ∀ z, ‖U z‖ ≤ B) (hbV : ∀ z, ‖V z‖ ≤ C)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun r => ‖spatialSharedAmplitude c U V r‖^2) μ := by
  let K := ((∫ ξ : Space d, ‖c ξ‖)*(B*C))*(sphereMeasure d).real univ
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (mul_nonneg hB hC))
    measureReal_nonneg
  apply (integrable_const (K^2)).mono'
    ((spatialSharedAmplitude_measurable c hcm U V hU hV).norm.pow_const 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro r
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hK).mpr
    (spatialSharedAmplitude_norm_le c hc U V hB hbU hbV r)

end Falconer

end OAI
