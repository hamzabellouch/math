import OAI.Geometry.CylinderCovering.Rational.DictionaryCoefficientsDefinitions

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace RationalDictionary

def uncenteredQuadraticCoefficient (d0 eta0 : ℝ) : ℝ :=
  (∫ u in (-c0)..c0, a0 d0 u + eta0) - uncenteredEnergy d0

def UncenteredExpansionStatement : Prop :=
  (∀ d0 : ℝ, 0 < d0 → ∀ eta0 : ℝ, 0 ≤ eta0 →
    Asymptotics.IsBigO (𝓝[>] (0 : ℝ))
      (fun k => orthonormalCost d0 eta0 k -
        (c0 + k ^ 2 * uncenteredQuadraticCoefficient d0 eta0)) (fun k => k ^ 4)) ∧
  (∀ d0 : ℝ, 0 < d0 → 0 < coefficientGap d0 →
    ∀ eta0 : ℝ, 0 < eta0 → eta0 < coefficientGap d0 / (2 * c0) →
      ∀ᶠ k : ℝ in 𝓝[>] (0 : ℝ), orthonormalCost d0 eta0 k < c0) ∧
  ∃ d0 : ℝ, 0 < d0 ∧ ∃ eta0 : ℝ, 0 < eta0 ∧
    eta0 < coefficientGap d0 / (2 * c0) ∧
    ∀ᶠ k : ℝ in 𝓝[>] (0 : ℝ), orthonormalCost d0 eta0 k < c0

end RationalDictionary

end

end OAI
