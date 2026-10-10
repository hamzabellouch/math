import OAI.Geometry.CylinderCovering.Rational.DictionaryDefinitions
import OAI.Geometry.CylinderCovering.Rational.RealizationDefinitions

namespace OAI

noncomputable section
open MeasureTheory
namespace RationalDictionary

def orthonormalWeight (d0 k : ℝ) (p : Plane) : ℝ :=
  1 / Real.sqrt (1 + k ^ 2 * (v1 d0 (p 0) (p 1) ^ 2 + v2 d0 (p 0) (p 1) ^ 2))

def orthonormalCost (d0 eta0 k : ℝ) : ℝ :=
  ∫ p in uncenteredDomain d0 eta0 k, orthonormalWeight d0 k p

def CostDictionaryStatement : Prop :=
  ∀ d0 : ℝ, 0 < d0 → ∀ eta0 k : ℝ,
    SlopeRational.weightedCost (centeredRegularization d0) (centeredTilt d0 k)
      (centeredPadding eta0 k) = orthonormalCost d0 eta0 k / 8

end RationalDictionary

end

end OAI
