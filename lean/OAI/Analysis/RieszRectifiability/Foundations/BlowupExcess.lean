import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.BlowupAffineGeometry

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem blowup_infDist_plane {d : ℕ} (a y : Ambient d) (r : ℝ) (hr : 0 < r)
    (S : AffineSubspace ℝ (Ambient d)) :
    infDist (r⁻¹ • (y - a)) (S : Set (Ambient d)) =
      r⁻¹ * infDist y (S.map (physicalAffine a r hr).toAffineMap : Set (Ambient d)) := by
  have h := physicalAffine_infDist a ((physicalAffine a r hr).symm y) r hr
    (S : Set (Ambient d))
  rw [(physicalAffine a r hr).apply_symm_apply] at h
  change infDist y (S.map (physicalAffine a r hr).toAffineMap : Set (Ambient d)) =
    r * infDist (r⁻¹ • (y - a)) (S : Set (Ambient d)) at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

theorem quadraticPlaneError_blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (S : AffineSubspace ℝ (Ambient d)) :
    quadraticPlaneError n (blowupMeasure n μ a r) 0 R S =
      quadraticPlaneError n μ a (r * R) (S.map (physicalAffine a r hr).toAffineMap) := by
  unfold quadraticPlaneError
  rw [blowupMeasure_setIntegral_ball n μ a 0 r R hr]
  simp only [smul_zero, add_zero, smul_eq_mul]
  simp_rw [blowup_infDist_plane a _ r hr S, mul_pow, integral_const_mul]
  simp only [mul_inv_rev, pow_add, inv_pow]
  ring

theorem squaredExcess_blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) :
    squaredExcess n (blowupMeasure n μ a r) 0 R = squaredExcess n μ a (r * R) := by
  unfold squaredExcess
  congr 1
  ext t
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S.map (physicalAffine a r hr).toAffineMap,
      isAffineNPlane_map_equiv n _ S hS, quadraticPlaneError_blowup n μ a r R hr S⟩
  · rintro ⟨T, hT, rfl⟩
    refine ⟨T.map (physicalAffine a r hr).symm.toAffineMap,
      isAffineNPlane_map_equiv n _ T hT, ?_⟩
    rw [quadraticPlaneError_blowup n μ a r R hr, affineSubspace_map_equiv_symm]

end

end RieszRectifiability

end OAI
