import OAI.Geometry.EinsteinFour.SphericalMoments

namespace OAI

/-! The fixed Hausdorff spherical measure is invariant under all orthogonal
changes of coordinates. This is the measure-theoretic input for the finite
second, fourth and sixth moment computation. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory

noncomputable section

def directionIsometry (e : FourSpace ≃ₗᵢ[ℝ] FourSpace) : Directions ≃ᵢ Directions where
  toFun q := ⟨e q.val, (e.norm_map q.val).trans q.property⟩
  invFun q := ⟨e.symm q.val, (e.symm.norm_map q.val).trans q.property⟩
  left_inv q := Subtype.ext (e.symm_apply_apply q.val)
  right_inv q := Subtype.ext (e.apply_symm_apply q.val)
  isometry_toFun := fun q r => e.isometry q.val r.val

theorem sphereMeasure_preserving (e : Directions ≃ᵢ Directions) :
    MeasurePreserving e sphereMeasure sphereMeasure := by
  constructor
  · exact e.continuous.measurable
  · unfold sphereMeasure
    rw [Measure.map_smul _ e.continuous.measurable.aemeasurable, e.map_hausdorffMeasure]

theorem sphereIntegral_isometry (e : Directions ≃ᵢ Directions) (f : Directions → ℝ) :
    (∫ q, f (e q) ∂sphereMeasure) = ∫ q, f q ∂sphereMeasure := by
  exact (sphereMeasure_preserving e).integral_comp e.toHomeomorph.measurableEmbedding f

end
end PositiveEinsteinFour.Angular

end OAI
