import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.BilateralBeta
import OAI.Analysis.RieszRectifiability.Flatness.BlowupAffineGeometry

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal Pointwise

theorem physicalAffine_image_blowup_support {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    physicalAffine a r hr '' (blowupMeasure n μ a r).support = μ.support := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (blowupMeasure_support_iff n μ a x r hr).mp hx
  · intro hy
    refine ⟨(physicalAffine a r hr).symm y, ?_, (physicalAffine a r hr).apply_symm_apply y⟩
    apply (blowupMeasure_support_iff n μ a _ r hr).mpr
    change physicalAffine a r hr ((physicalAffine a r hr).symm y) ∈ μ.support
    simpa only [(physicalAffine a r hr).apply_symm_apply] using! hy

theorem directedBallDeviation_physical {d : ℕ} (s t : Set (Ambient d))
    (a x : Ambient d) (r R : ℝ) (hr : 0 < r) :
    directedBallDeviation (physicalAffine a r hr '' s) (physicalAffine a r hr '' t)
      (physicalAffine a r hr x) (r * R) = r * directedBallDeviation s t x R := by
  have hset : ball (physicalAffine a r hr x) (r * R) ∩ physicalAffine a r hr '' s =
      physicalAffine a r hr '' (ball x R ∩ s) := by
    ext y
    constructor
    · rintro ⟨hy, z, hz, rfl⟩
      refine ⟨z, ⟨?_, hz⟩, rfl⟩
      have hzball : z ∈ physicalAffine a r hr ⁻¹'
          ball (physicalAffine a r hr x) (r * R) := hy
      rwa [physicalAffine_preimage_ball a x r R hr] at hzball
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, ⟨z, hz.2, rfl⟩⟩
      have hzball : z ∈ physicalAffine a r hr ⁻¹'
          ball (physicalAffine a r hr x) (r * R) := by
        rw [physicalAffine_preimage_ball a x r R hr]
        exact hz.1
      exact hzball
  unfold directedBallDeviation
  rw [hset, Set.image_image]
  simp_rw [physicalAffine_infDist a _ r hr t]
  calc
    _ = sSup (r • ((fun z => infDist z t) '' (ball x R ∩ s))) := by
      congr 1
      rw [← Set.image_smul, Set.image_image]
      rfl
    _ = _ := Real.sSup_smul_of_nonneg hr.le _

theorem bilateralPlaneError_blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (S : AffineSubspace ℝ (Ambient d)) :
    bilateralPlaneError (blowupMeasure n μ a r) 0 R S =
      bilateralPlaneError μ a (r * R) (S.map (physicalAffine a r hr).toAffineMap) := by
  have hforward := directedBallDeviation_physical (blowupMeasure n μ a r).support
    (S : Set (Ambient d)) a 0 r R hr
  have hreverse := directedBallDeviation_physical (S : Set (Ambient d))
    (blowupMeasure n μ a r).support a 0 r R hr
  rw [physicalAffine_image_blowup_support n μ a r hr] at hforward hreverse
  have hzero : physicalAffine a r hr 0 = a := by
    rw [physicalAffine_apply, smul_zero, add_zero]
  rw [hzero] at hforward hreverse
  unfold bilateralPlaneError
  rw [AffineSubspace.coe_map]
  change _ = (directedBallDeviation μ.support
    (physicalAffine a r hr '' (S : Set (Ambient d))) a (r * R) +
    directedBallDeviation (physicalAffine a r hr '' (S : Set (Ambient d)))
      μ.support a (r * R)) / (r * R)
  rw [hforward, hreverse, ← mul_add, mul_div_mul_left _ _ hr.ne']

theorem bilateralBeta_blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) :
    bilateralBeta n (blowupMeasure n μ a r) 0 R = bilateralBeta n μ a (r * R) := by
  unfold bilateralBeta
  congr 1
  ext t
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S.map (physicalAffine a r hr).toAffineMap,
      isAffineNPlane_map_equiv n _ S hS, bilateralPlaneError_blowup n μ a r R hr S⟩
  · rintro ⟨T, hT, rfl⟩
    refine ⟨T.map (physicalAffine a r hr).symm.toAffineMap,
      isAffineNPlane_map_equiv n _ T hT, ?_⟩
    rw [bilateralPlaneError_blowup n μ a r R hr, affineSubspace_map_equiv_symm]

end

end RieszRectifiability

end OAI
