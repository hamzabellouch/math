import OAI.Geometry.CylinderCovering.Rational.DictionaryDefinitions

namespace OAI

noncomputable section
namespace RationalDictionary

def UncenteredThresholdStatement : Prop :=
  ∀ d0 eta0 : ℝ, 0 < d0 → 0 < eta0 → ∃ δ : ℝ, 0 < δ ∧
    ∀ k r u z : ℝ, 0 < k → k < δ → |r| ≤ 2 * c0 →
      0 ≤ z → z ≤ 2 → |u| ≤ c0 * z → z ≤ threshold d0 k r u →
      ∃ p ∈ uncenteredDomain d0 eta0 k, lineMap d0 k r p = vec2 u z

def UncenteredCoverageStatement : Prop :=
  ∀ d0 eta0 : ℝ, 0 < d0 → 0 < eta0 → ∃ δ : ℝ, 0 < δ ∧
    ∀ k : ℝ, 0 < k → k < δ →
      RationalSimilarity.uncenteredTetrahedron ⊆
        uncenteredFirstSweep d0 eta0 k ∪ uncenteredSecondSweep d0 eta0 k

end RationalDictionary

end

end OAI
