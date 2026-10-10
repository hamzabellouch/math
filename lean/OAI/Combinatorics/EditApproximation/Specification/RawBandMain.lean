import OAI.Combinatorics.EditApproximation.Specification.RawBandPipelineFootprintBridges
import OAI.Combinatorics.EditApproximation.Definitions

namespace OAI.EditApproximation
open Filter MeasureTheory
attribute [local instance] queryRoundsNeZero

theorem almostLinearEditDistanceRawBand (epsilon : BinaryFraction)
    (hepsilon : 0 < epsilon.value) (_hepsilonOne : epsilon.value < 1)
    :
    (∀ (source target : List ℤ) (N : ℕ), source.length + target.length ≤ N →
      (2 / 3 : ℝ) ≤ (computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon).real
        {outcome | EditDistortion.edit source target ≤ integerBinaryAnswerRawBand source target N epsilon outcome ∧
          (integerBinaryAnswerRawBand source target N epsilon outcome : ℝ) ≤
            (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target}) ∧
    (∀ (source target : List ℤ) (N : ℕ), source = target → ∀ outcome,
      integerBinaryAnswerRawBand source target N epsilon outcome = 0) ∧
    (∀ (C : ℕ) (eta : ℝ), 0 < eta → ∀ᶠ N : ℕ in atTop,
      ∀ source target : List ℤ, source.length + target.length ≤ N →
        (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
        (∫ outcome, integerBinaryWorkRawBand source target N epsilon outcome
          ∂computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon) ≤
            (N + 2 : ℝ) ^ (1 + eta)) ∧
    (∀ C : ℕ, ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ,
      source.length + target.length ≤ N →
        (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
        ∀ outcome, integerBinarySpaceFootprintRawBand source target N epsilon outcome ≤ (N + 2) ^ (C + 65564)) := by
  simpa only [integerBinaryAnswerRawBand_eq, integerBinaryWorkRawBand_eq,
    integerBinarySpaceFootprintRawBand_eq] using
    almostLinearEditDistance_main epsilon hepsilon _hepsilonOne

end OAI.EditApproximation
