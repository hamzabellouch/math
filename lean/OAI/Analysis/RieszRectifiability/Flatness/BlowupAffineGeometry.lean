import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.LeastSquaredExcess
import OAI.Analysis.RieszRectifiability.Nets.BlowupRadiusGeometry

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal Pointwise

def physicalAffine {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    Ambient d ≃ᵃ[ℝ] Ambient d where
  toEquiv :=
    { toFun := fun x => a + r • x
      invFun := fun y => r⁻¹ • (y - a)
      left_inv := by
        intro x
        change r⁻¹ • ((a + r • x) - a) = x
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
      right_inv := by
        intro y
        change a + r • (r⁻¹ • (y - a)) = y
        rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
        abel }
  linear := LinearEquiv.smulOfNeZero ℝ (Ambient d) r hr.ne'
  map_vadd' := by
    intro x v
    change a + r • (v + x) = r • v + (a + r • x)
    rw [smul_add]
    abel

def physicalHomeomorph {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    Ambient d ≃ₜ Ambient d where
  toEquiv := (physicalAffine a r hr).toEquiv
  continuous_toFun := by change Continuous (fun x => a + r • x); fun_prop
  continuous_invFun := by change Continuous (fun y => r⁻¹ • (y - a)); fun_prop

theorem physicalAffine_apply {d : ℕ} (a x : Ambient d) (r : ℝ) (hr : 0 < r) :
    physicalAffine a r hr x = a + r • x := rfl

theorem physicalAffine_symm_apply {d : ℕ} (a y : Ambient d) (r : ℝ) (hr : 0 < r) :
    (physicalAffine a r hr).symm y = r⁻¹ • (y - a) := rfl

theorem isAffineNPlane_map_equiv {d : ℕ} (n : ℕ)
    (e : Ambient d ≃ᵃ[ℝ] Ambient d) (S : AffineSubspace ℝ (Ambient d))
    (hS : IsAffineNPlane n S) : IsAffineNPlane n (S.map e.toAffineMap) := by
  refine ⟨hS.1.image e, ?_⟩
  rw [AffineSubspace.map_direction, AffineEquiv.linear_toAffineMap,
    e.linear.finrank_map_eq, hS.2]

theorem affineSubspace_map_equiv_symm {d : ℕ}
    (e : Ambient d ≃ᵃ[ℝ] Ambient d) (S : AffineSubspace ℝ (Ambient d)) :
    (S.map e.symm.toAffineMap).map e.toAffineMap = S := by
  apply SetLike.coe_injective
  change e '' (e.symm '' (S : Set (Ambient d))) = (S : Set (Ambient d))
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa only [e.apply_symm_apply] using! hz
  · intro hx
    exact ⟨e.symm x, ⟨x, hx, rfl⟩, e.apply_symm_apply x⟩

theorem physicalAffine_infDist {d : ℕ} (a x : Ambient d) (r : ℝ) (hr : 0 < r)
    (s : Set (Ambient d)) :
    infDist (physicalAffine a r hr x) (physicalAffine a r hr '' s) = r * infDist x s := by
  have himage : physicalAffine a r hr '' s = (fun y : Ambient d => a + y) '' (r • s) := by
    rw [← Set.image_smul, Set.image_image]
    rfl
  have htranslate : Isometry (fun y : Ambient d => a + y) := by
    apply Isometry.of_dist_eq
    intro x y
    exact dist_add_left a x y
  rw [physicalAffine_apply, himage, Metric.infDist_image htranslate,
    infDist_smul₀ hr.ne', Real.norm_of_nonneg hr.le]

theorem physicalAffine_preimage_ball {d : ℕ} (a x : Ambient d) (r R : ℝ) (hr : 0 < r) :
    physicalAffine a r hr ⁻¹' ball (physicalAffine a r hr x) (r * R) = ball x R := by
  ext y
  have hd : dist (physicalAffine a r hr y) (physicalAffine a r hr x) = r * dist y x := by
    simp only [physicalAffine_apply, dist_add_left, dist_smul₀, Real.norm_of_nonneg hr.le]
  simp only [mem_preimage, mem_ball, hd, mul_lt_mul_iff_right₀ hr]

theorem blowupMeasure_setIntegral_ball {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (μ : Measure (Ambient d))
    (a x : Ambient d) (r R : ℝ) (hr : 0 < r) (f : Ambient d → E) :
    (∫ y in ball x R, f y ∂blowupMeasure n μ a r) =
      (r ^ n)⁻¹ • ∫ y in ball (a + r • x) (r * R), f (r⁻¹ • (y - a)) ∂μ := by
  rw [blowupMeasure, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (r ^ n)⁻¹)]
  have he : MeasurableEmbedding (fun y : Ambient d => r⁻¹ • (y - a)) :=
    (physicalHomeomorph a r hr).symm.measurableEmbedding
  rw [he.setIntegral_map, blowup_preimage_ball a x r R hr]

end

end RieszRectifiability

end OAI
