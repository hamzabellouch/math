import OAI.Combinatorics.ProgressionColoring.AnchoredPatternDefinitions
import OAI.Combinatorics.ProgressionColoring.OuterWordTests

namespace OAI

/-! The exact two balancing properties consumed by the geometric dichotomy.
The existence proof, including actual pattern counts, is in
`EligibleOuterColoring`. -/

namespace QuantitativeVanDerWaerden

/-- The two balancing properties of the selected outer label coloring. -/
structure OuterBalanced {D k : ℕ} (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh)
    (eta : ℝ) (lambda M : ℕ)
    (words : Finset (Fin k → FullLabel D (Fin n) A.Label)) (periods : Finset ℕ)
    (color : FullLabel D (Fin n) A.Label → Bool) : Prop where
  global_words : ∀ word ∈ words,
    k ≤ 10 * (OuterWordTests.lightPositions M word).card → ∀ b,
      (OuterWordTests.lightPositions M word).card ≤
        4 * ((OuterWordTests.lightPositions M word).filter
          fun j => color (word j) = b).card
  eligible_patterns : ∀ h ∈ periods, ∀ t : Fin D → Fin h,
    ∀ R : AnchoredPatterns.Realization D,
      AnchoredPatterns.EligibleRealization n hn A eta lambda t R → ∀ b,
        (AnchoredPatterns.regularPositions eta R lambda t).card ≤
          4 * ((AnchoredPatterns.regularPositions eta R lambda t).filter
            fun z => color (AnchoredPatterns.fullLabel n hn A R lambda t z) = b).card

end QuantitativeVanDerWaerden

end OAI
