import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.BlowupRieszOperator
import OAI.Analysis.RieszRectifiability.Kernel.OscillationTests

namespace OAI

/-!
# Scalar Riesz pairings under blowup

Change of variables for normalized blowup measures transfers the near and far parts
of the scalar Riesz pairing. Rescaling the localization ball and pulling back the test
function gives the exact factor `(r ^ n)⁻¹` in the pairing identity.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem blowupMeasure_integral {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 < r) (f : Ambient d → E) :
    (∫ y, f y ∂blowupMeasure n μ a r) =
      (r ^ n)⁻¹ • ∫ y, f (r⁻¹ • (y - a)) ∂μ := by
  have he : MeasurableEmbedding (fun y : Ambient d => r⁻¹ • (y - a)) :=
    (physicalHomeomorph a r hr).symm.measurableEmbedding
  rw [blowupMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (r ^ n)⁻¹), he.integral_map]

theorem blowupMeasure_integral_prod_restrict {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    [SFinite μ] (a : Ambient d) (r : ℝ) (hr : 0 < r) (s t : Set (Ambient d))
    (f : Ambient d × Ambient d → ℝ) :
    (∫ q, f q ∂((blowupMeasure n μ a r).restrict s).prod
      ((blowupMeasure n μ a r).restrict t)) =
      ((r ^ n)⁻¹) ^ 2 * ∫ q, f (r⁻¹ • (q.1 - a), r⁻¹ • (q.2 - a))
        ∂(μ.restrict ((fun y => r⁻¹ • (y - a)) ⁻¹' s)).prod
          (μ.restrict ((fun y => r⁻¹ • (y - a)) ⁻¹' t)) := by
  let e := (physicalHomeomorph a r hr).symm.toMeasurableEquiv
  have he : MeasurableEmbedding (fun y : Ambient d => r⁻¹ • (y - a)) := e.measurableEmbedding
  have heprod : MeasurableEmbedding (Prod.map (fun y : Ambient d => r⁻¹ • (y - a))
      (fun y : Ambient d => r⁻¹ • (y - a))) := (e.prodCongr e).measurableEmbedding
  simp only [blowupMeasure, Measure.restrict_smul, he.restrict_map]
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, integral_smul_measure,
    Measure.map_prod_map _ _ he.measurable he.measurable, heprod.integral_map]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ (r ^ n)⁻¹),
    smul_eq_mul, pow_two]
  rfl

theorem kernel_normalized {d : ℕ} (n : ℕ) (a x y : Ambient d) (r : ℝ) (hr : 0 < r) :
    kernel n (r⁻¹ • (x - a)) (r⁻¹ • (y - a)) = r ^ n • kernel n x y := by
  have h := kernel_physicalAffine n a ((physicalAffine a r hr).symm x)
    ((physicalAffine a r hr).symm y) r hr
  rw [(physicalAffine a r hr).apply_symm_apply, (physicalAffine a r hr).apply_symm_apply] at h
  rw [h, smul_smul, mul_inv_cancel₀ (pow_ne_zero n hr.ne'), one_smul]
  rfl

theorem blowup_preimage_closedExterior {d : ℕ} (a : Ambient d) (r R : ℝ) (hr : 0 < r) :
    (fun y : Ambient d => r⁻¹ • (y - a)) ⁻¹' closedExterior 0 R = closedExterior a (r * R) := by
  ext y
  have hdist : dist a y = r * dist (0 : Ambient d) (r⁻¹ • (y - a)) := by
    have h := physicalAffine_dist a 0 ((physicalAffine a r hr).symm y) r hr
    rw [(physicalAffine a r hr).apply_symm_apply] at h
    simpa only [physicalAffine_apply, smul_zero, add_zero, physicalAffine_symm_apply] using! h
  simp only [closedExterior, mem_preimage, mem_ofPred_eq, hdist, mul_le_mul_iff_right₀ hr]

theorem rieszScalarPairing_blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) [SFinite μ]
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (e : Ambient d) (φ : Ambient d → ℝ) :
    rieszScalarPairing n (blowupMeasure n μ a r) 0 R e φ =
      (r ^ n)⁻¹ * rieszScalarPairing n μ a (r * R) e (fun y => φ (r⁻¹ • (y - a))) := by
  have hi (q : Ambient d × Ambient d) :
      rieszInteriorIntegrand n e φ (r⁻¹ • (q.1 - a), r⁻¹ • (q.2 - a)) =
        r ^ n * rieszInteriorIntegrand n e (fun y => φ (r⁻¹ • (y - a))) q := by
    unfold rieszInteriorIntegrand
    dsimp only
    rw [kernel_normalized n a q.1 q.2 r hr, real_inner_smul_right]
    ring
  have hf (q : Ambient d × Ambient d) :
      rieszFarIntegrand n e φ 0 (r⁻¹ • (q.1 - a), r⁻¹ • (q.2 - a)) =
        r ^ n * rieszFarIntegrand n e (fun y => φ (r⁻¹ • (y - a))) a q := by
    unfold rieszFarIntegrand
    dsimp only
    have hzero : r⁻¹ • (a - a) = (0 : Ambient d) := by simp
    rw [← hzero, kernel_normalized n a q.1 q.2 r hr, kernel_normalized n a a q.2 r hr,
      ← smul_sub, real_inner_smul_right]
    ring
  unfold rieszScalarPairing
  dsimp only
  rw [blowupMeasure_integral_prod_restrict n μ a r hr,
    blowupMeasure_integral_prod_restrict n μ a r hr,
    blowup_preimage_ball a 0 r R hr, blowup_preimage_closedExterior a r R hr]
  simp only [smul_zero, add_zero]
  simp_rw [hi, hf, integral_const_mul]
  have hcancel : ((r ^ n)⁻¹) ^ 2 * r ^ n = (r ^ n)⁻¹ := by
    field_simp
  have hscale (z : ℝ) : ((r ^ n)⁻¹) ^ 2 * (r ^ n * z) = (r ^ n)⁻¹ * z := by
    rw [← mul_assoc, hcancel]
  simp_rw [hscale]
  ring

end

end RieszRectifiability

end OAI
