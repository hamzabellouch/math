import OAI.Combinatorics.EditApproximation.AlmostLinearConditional
import OAI.Combinatorics.EditApproximation.Probability.BernsteinFinite

namespace OAI

/-! A uniform binary approximation scheme for edit distance.
The finite Bernstein inequality supplies the concentration bounds for the
initial estimator and the refinement samples. -/

namespace EditApproximation
open MeasureTheory Filter

/-- Finite product-measure concentration for the initial estimator and refinement. -/
theorem computedBernsteinInputs (N : ℕ) : ComputedBernsteinInputs N := by
  constructor
  · exact finiteBernsteinInput _
  · intro b h
    exact finiteBernsteinInput _

/-- A uniform almost-linear approximation scheme. The same binary algorithm
satisfies the approximation, equality, expected-work and space bounds. -/
theorem almostLinearEditDistance (epsilon : BinaryFraction)
    (hepsilon : 0 < epsilon.value) (_hepsilonOne : epsilon.value < 1)
    :
    (∀ (source target : List ℤ) (N : ℕ), source.length + target.length ≤ N →
      (2 / 3 : ℝ) ≤ (computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon).real
        {outcome | EditDistortion.edit source target ≤ integerBinaryAnswer source target N epsilon outcome ∧
          (integerBinaryAnswer source target N epsilon outcome : ℝ) ≤
            (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target}) ∧
    (∀ (source target : List ℤ) (N : ℕ), source = target → ∀ outcome,
      integerBinaryAnswer source target N epsilon outcome = 0) ∧
    (∀ (C : ℕ) (eta : ℝ), 0 < eta → ∀ᶠ N : ℕ in atTop,
      ∀ source target : List ℤ, source.length + target.length ≤ N →
        (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
        (∫ outcome, integerBinaryWork source target N epsilon outcome
          ∂computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon) ≤
            (N + 2 : ℝ) ^ (1 + eta)) ∧
    (∀ C : ℕ, ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ,
      source.length + target.length ≤ N →
        (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
        ∀ outcome, integerBinarySpace source target N epsilon outcome ≤ (N + 2) ^ (C + 65564)) := by
  exact almostLinearEditDistance_conditional epsilon hepsilon _hepsilonOne computedBernsteinInputs

end EditApproximation

end OAI
