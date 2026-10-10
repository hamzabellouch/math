import OAI.Geometry.CylinderCovering.Rational.DictionaryCoefficientsDefinitions
import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace RationalDictionary

def LogarithmicApproximationStatement : Prop :=
  ∀ d0 : ℝ, 0 < d0 → ∀ k : ℝ, 0 < k → k < d0 / (1 + d0) →
    ∀ eta0 : ℝ, ∀ e : ℝ, 0 < e →
      RuledApproximation.HasFiniteCover RuledApproximation.Cylinder.openBounded
        (uncenteredFirstSweep d0 eta0 k) (orthonormalCost d0 eta0 k + e) ∧
      RuledApproximation.HasFiniteCover RuledApproximation.Cylinder.openBounded
        (uncenteredSecondSweep d0 eta0 k) (orthonormalCost d0 eta0 k + e)

def HasStrictLogarithmicCover (d0 eta0 k : ℝ) : Prop :=
  ∃ n m : ℕ, ∃ C : Fin n → RuledApproximation.Cylinder,
    ∃ D : Fin m → RuledApproximation.Cylinder,
      (∀ i, (C i).openBounded) ∧ (∀ j, (D j).openBounded) ∧
      uncenteredFirstSweep d0 eta0 k ⊆ RuledApproximation.familySet C ∧
      uncenteredSecondSweep d0 eta0 k ⊆ RuledApproximation.familySet D ∧
      RationalSimilarity.uncenteredTetrahedron ⊆
        RuledApproximation.familySet C ∪ RuledApproximation.familySet D ∧
      RuledApproximation.familyArea C + RuledApproximation.familyArea D <
        CylinderCovering.minimumShadowArea RationalSimilarity.uncenteredTetrahedron / 2 ∧
      CylinderCovering.relativeCost RationalSimilarity.uncenteredTetrahedron C +
        CylinderCovering.relativeCost RationalSimilarity.uncenteredTetrahedron D < 1 / 2

def LogarithmicStatement : Prop :=
  LogarithmicApproximationStatement ∧
  CylinderCovering.minimumShadowArea RationalSimilarity.uncenteredTetrahedron = 4 * c0 ∧
  (∀ d0 : ℝ, 0 < d0 → 0 < coefficientGap d0 →
    ∀ eta0 : ℝ, 0 < eta0 → eta0 < coefficientGap d0 / (2 * c0) →
      ∀ᶠ k : ℝ in 𝓝[>] (0 : ℝ),
        orthonormalCost d0 eta0 k < c0 ∧ HasStrictLogarithmicCover d0 eta0 k) ∧
  ∃ d0 : ℝ, 0 < d0 ∧ ∃ eta0 : ℝ, 0 < eta0 ∧
    eta0 < coefficientGap d0 / (2 * c0) ∧
    ∀ᶠ k : ℝ in 𝓝[>] (0 : ℝ),
      orthonormalCost d0 eta0 k < c0 ∧ HasStrictLogarithmicCover d0 eta0 k

end RationalDictionary

end

end OAI
