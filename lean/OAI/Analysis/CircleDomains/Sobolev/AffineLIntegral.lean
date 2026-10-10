import OAI.Analysis.CircleDomains.Sobolev.AffineLpTransport
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace OAI

/-! Nonnegative integrals under the physical affine change of variables,
including measurable indicators and possibly infinite energies. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma lintegral_planarAffine (a : EuclideanPlane) {s : ℝ} (hs : 0 < s)
    (f : EuclideanPlane → ℝ≥0∞) :
    (∫⁻ x, f (a+s • x)) = ENNReal.ofReal ((s^2)⁻¹) * ∫⁻ y, f y := by
  have he := (planarAffineHomeomorph a s hs.ne').toMeasurableEquiv.measurableEmbedding.lintegral_map (μ := volume) f
  change (∫⁻ y, f y ∂Measure.map (fun x : EuclideanPlane => a+s • x) volume) =
    ∫⁻ x, f (a+s • x) at he
  rw [← he, map_volume_planarAffine a hs, lintegral_smul_measure, smul_eq_mul]

lemma scaled_lintegral_planarAffine (a : EuclideanPlane) {s : ℝ} (hs : 0 < s)
    (f : EuclideanPlane → ℝ≥0∞) :
    ENNReal.ofReal (s^2) * (∫⁻ x, f (a+s • x)) = ∫⁻ y, f y := by
  rw [lintegral_planarAffine a hs, ← mul_assoc,
    ← ENNReal.ofReal_mul (sq_nonneg s), mul_inv_cancel₀ (pow_ne_zero 2 hs.ne'),
    ENNReal.ofReal_one, one_mul]

end CircleDomainRigidity

end

end OAI
