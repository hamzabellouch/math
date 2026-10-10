import OAI.Analysis.FiniteFactor.CrossedProduct.WeightedShiftField
import OAI.Analysis.FiniteFactor.CrossedProduct.TorusModel

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- The proved source field on the actual compact sampling torus. -/
def sourceTorusOperatorField
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (z : SourceTorus) :
    SourceFiberHilbert →L[ℂ] SourceFiberHilbert :=
  sourceOperatorField H (sourceTorusRepresentative z)

theorem sourceTorusOperatorField_stronglyMeasurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (v : SourceFiberHilbert) :
    StronglyMeasurable (fun z => sourceTorusOperatorField H z v) :=
  (sourceOperatorField_stronglyMeasurable H v).comp_measurable sourceTorusRepresentative_preserving.measurable

theorem sourceTorusOperatorField_norm
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (z : SourceTorus) :
    ‖sourceTorusOperatorField H z‖ ≤ ‖H‖ := sourceOperatorField_norm H _

theorem sourceTorusOperatorField_projection (θ : SourceCoordinate → ℝ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p) :
    ∀ᵐ z ∂sourceTorusHaar, IsStarProjection (sourceTorusOperatorField p z) :=
  sourceTorusRepresentative_preserving.quasiMeasurePreserving.ae
    (sourceOperatorField_projection θ hp hproj)

theorem sourceTorusOperatorField_invariant (θ : SourceCoordinate → ℝ)
    {p T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hT : T ∈ sourceAlgebra θ)
    (hinv : (1-p)*T*p = 0) :
    ∀ᵐ z ∂sourceTorusHaar,
      (1-sourceTorusOperatorField p z)*sourceTorusOperatorField T z*sourceTorusOperatorField p z = 0 :=
  sourceTorusRepresentative_preserving.quasiMeasurePreserving.ae
    (sourceOperatorField_invariant θ hp hT hinv)

theorem sourceTorusOperatorField_sourceOperator_pow (θ : SourceCoordinate → ℝ)
    (hθ : SourceAngles θ) (q : ℕ) :
    ∀ᵐ z ∂sourceTorusHaar, ∀ (v : SourceFiberHilbert) (k : ℤ),
      (sourceTorusOperatorField
        (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg ^ q) z v) k =
        (sourceCocycle θ sourceLogWeight q
          (coordinateRotate θ (k - (q : ℤ)) (sourceTorusRepresentative z)) : ℂ) *
          v (k - (q : ℤ)) :=
  sourceTorusRepresentative_preserving.quasiMeasurePreserving.ae
    (sourceOperatorField_sourceOperator_pow θ hθ q)

end
end FiniteFactor

end OAI
