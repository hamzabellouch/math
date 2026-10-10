import OAI.Analysis.IrrationalRotation.Model.CircleParameters

namespace OAI

noncomputable section
open scoped BigOperators
namespace Invariant233.CircleParameterData

def orbitGraphDensity (p : CircleParameterData) (θ : ℝ) (j n : ℕ)
    (x : Circle) : ℝ :=
  ∏ i ∈ p.block j, kernel (p.m j) (p.coordinate i x)
    (Int.fract ((n : ℝ) * p.alpha θ i))

def rationalGraphGood (p : CircleParameterData) (A j : ℕ) : Set Circle :=
  {x | (∀ i, A ≤ i → i ≤ p.blockEnd (j - 1) →
      p.coordinate i x < 1 - (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j) ∧
    ∀ s, j < s → ∀ i ∈ p.block s,
      p.coordinate i x < 1 - 2 * p.Q j / p.N s}

def rationalGraphPrefixCost (p : CircleParameterData) (A : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (A - 1), p.flattenedCost k

def rationalGraphBad (p : CircleParameterData) (A j : ℕ) : Set Circle :=
  (p.rationalGraphGood A j)ᶜ

end Invariant233.CircleParameterData

end

end OAI
