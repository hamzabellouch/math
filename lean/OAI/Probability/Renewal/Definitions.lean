import Mathlib

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace HoneycombLocal

def sumLaw (p : PMF ℕ) : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | k + 1 => p.bind (fun j => (sumLaw p k).map (fun r => j + r))

def renewalMass (p : PMF ℕ) (m : ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, sumLaw p (k + 1) m

def SpanOne (p : PMF ℕ) : Prop :=
  AddSubgroup.closure {z : ℤ | ∃ j ∈ p.support, ∃ k ∈ p.support, z = (j : ℤ) - k} = ⊤

def laplace (p : PMF ℕ) (u : ℝ) : ℝ :=
  ∫ j, Real.exp (-u * (j : ℝ)) ∂p.toMeasure

def BoundedPowerInput (p : PMF ℕ) (a : ℝ) : Prop :=
  ∃ c > 0, ∃ C > 0, ∃ x₀ > 0,
    (∀ x ≥ x₀, p.toMeasure.real {j | x < (j : ℝ)} ≤ C * x ^ (-a)) ∧
    (∀ u > 0, u ≤ x₀⁻¹ →
      c * u ^ a ≤ 1 - laplace p u ∧ 1 - laplace p u ≤ C * u ^ a)

end HoneycombLocal

end

end OAI
