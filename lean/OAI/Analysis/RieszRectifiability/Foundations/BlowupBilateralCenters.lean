import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.BlowupBilateralBeta

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem bilateralPlaneError_blowup_at {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a b : Ambient d) (s R : ℝ) (hs : 0 < s) (S : AffineSubspace ℝ (Ambient d)) :
    bilateralPlaneError (blowupMeasure n μ a s) b R S =
      bilateralPlaneError μ (a + s • b) (s * R) (S.map (physicalAffine a s hs).toAffineMap) := by
  have hforward := directedBallDeviation_physical (blowupMeasure n μ a s).support
    (S : Set (Ambient d)) a b s R hs
  have hreverse := directedBallDeviation_physical (S : Set (Ambient d))
    (blowupMeasure n μ a s).support a b s R hs
  rw [physicalAffine_image_blowup_support n μ a s hs, physicalAffine_apply] at hforward hreverse
  unfold bilateralPlaneError
  rw [AffineSubspace.coe_map]
  change _ = (directedBallDeviation μ.support
    (physicalAffine a s hs '' (S : Set (Ambient d))) (a + s • b) (s * R) +
    directedBallDeviation (physicalAffine a s hs '' (S : Set (Ambient d)))
      μ.support (a + s • b) (s * R)) / (s * R)
  rw [hforward, hreverse, ← mul_add, mul_div_mul_left _ _ hs.ne']

theorem bilateralBeta_blowup_at {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a b : Ambient d) (s R : ℝ) (hs : 0 < s) :
    bilateralBeta n (blowupMeasure n μ a s) b R = bilateralBeta n μ (a + s • b) (s * R) := by
  unfold bilateralBeta
  congr 1
  ext t
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S.map (physicalAffine a s hs).toAffineMap,
      isAffineNPlane_map_equiv n _ S hS, bilateralPlaneError_blowup_at n μ a b s R hs S⟩
  · rintro ⟨T, hT, rfl⟩
    refine ⟨T.map (physicalAffine a s hs).symm.toAffineMap,
      isAffineNPlane_map_equiv n _ T hT, ?_⟩
    rw [bilateralPlaneError_blowup_at n μ a b s R hs, affineSubspace_map_equiv_symm]

end

end RieszRectifiability

end OAI
