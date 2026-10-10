import OAI.Geometry.CylinderCovering.Rational.DictionaryDefinitions
import OAI.Geometry.CylinderCovering.Rational.RealizationDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory
namespace RationalDictionary

def CoordinateCostStatement : Prop :=
  ∀ d0 : ℝ, 0 < d0 → ∀ eta0 k : ℝ,
    RationalSimilarity.phi '' RationalSimilarity.uncenteredTetrahedron =
      SlopeRational.referenceTetrahedron ∧
    RationalSimilarity.phi '' uncenteredFirstSweep d0 eta0 k =
      SlopeRational.lowerSweep (centeredRegularization d0) (centeredTilt d0 k)
        (centeredPadding eta0 k) ∧
    RationalSimilarity.phi '' uncenteredSecondSweep d0 eta0 k =
      SlopeRational.upperSweep (centeredRegularization d0) (centeredTilt d0 k)
        (centeredPadding eta0 k) ∧
    SlopeRational.weightedCost (centeredRegularization d0) (centeredTilt d0 k)
      (centeredPadding eta0 k) = uncenteredCost d0 eta0 k / 8 ∧
    centeredPadding eta0 k = centeredMargin d0 eta0 * centeredTilt d0 k ^ 2 ∧
    ∀ S : Set Space,
      (Measure.euclideanHausdorffMeasure 2 (RationalSimilarity.phi '' S)).toReal =
        (1 / 8 : ℝ) * (Measure.euclideanHausdorffMeasure 2 S).toReal

end RationalDictionary

end

end OAI
