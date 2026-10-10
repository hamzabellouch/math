import OAI.Combinatorics.EditApproximation.Binary.IntegerBinaryAccuracy
import OAI.Combinatorics.EditApproximation.Binary.IntegerBinarySpace

namespace OAI

/-! An edit-distance approximation scheme conditional on finite scalar
Bernstein concentration (Tropp, ACM217, corrected 2023, Theorem 4.16).
The same uniform binary algorithm is used in all four clauses. -/

namespace EditApproximation
open MeasureTheory Filter

/-- For each fixed binary accuracy in `(0,1)`, the concrete uniform algorithm
has success probability at least `2/3`, deterministic zero on equal inputs,
worst-case expected almost-linear time including preprocessing and sampling,
and polynomial space on every outcome. Alphabet bounds are analysis parameters,
not inputs to the algorithm. The finite initial range uses exact suffix DP. -/
theorem almostLinearEditDistance_conditional (epsilon : BinaryFraction)
    (hepsilon : 0 < epsilon.value) (_hepsilonOne : epsilon.value < 1)
    (bernstein : ∀ N, ComputedBernsteinInputs N) :
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
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro source target N hsize
    exact integerBinaryAnswer_conditional_accuracy source target N epsilon hepsilon hsize (bernstein N)
  · intro source target N heq outcome
    exact integerBinaryAnswer_equal source target N epsilon heq outcome
  · intro C eta heta
    exact integerBinaryWork_expected_near_linear C epsilon hepsilon eta heta
  · intro C
    exact integerBinarySpace_polynomial C epsilon hepsilon

/-- The cutoff selects an exact answer, rather than leaving the small-input
regime outside the uniform algorithm's correctness statement. -/
theorem integerBinaryAnswer_fallback (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction)
    (hsmall : ¬ physicalLargeInput N epsilon) (outcome) :
    integerBinaryAnswer source target N epsilon outcome = EditDistortion.edit source target := by
  simp only [integerBinaryAnswer, hsmall, ite_false, exactSuffixAnswer_eq_edit, integerSymbols_edit]

end EditApproximation

end OAI
