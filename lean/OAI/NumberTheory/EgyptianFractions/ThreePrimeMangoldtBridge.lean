import OAI.NumberTheory.EgyptianFractions.ThreePrimeMangoldt
import OAI.NumberTheory.EgyptianFractions.ThreePrimeWeighted

namespace OAI
noncomputable section
open Filter

namespace Problem337

/-- The independently defined prime-weighted counts are identical. -/
lemma primeTripleLogSum_eq_weightedSupplyPrimeTriples (u : ℕ) :
    primeTripleLogSum u = weightedSupplyPrimeTriples u := rfl

/-- The standard quadratic lower bound for the von Mangoldt convolution is
sufficient for the exact arithmetic hypothesis used in the Egyptian-fraction
construction. The genuinely analytic lower bound remains an explicit premise. -/
theorem quantitativeThreePrimeLowerBound_of_mangoldt
    (hmain : ∃ c : ℝ, 0 < c ∧ ∀ᶠ u : ℕ in atTop, Odd u →
      c * (u : ℝ) ^ 2 ≤ mangoldtTripleSum u) :
    QuantitativeThreePrimeLowerBound := by
  obtain ⟨c, hc, hmain⟩ := hmain
  apply quantitativeThreePrimeLowerBound_of_weighted
  refine ⟨c / 2, by positivity, ?_⟩
  simpa only [primeTripleLogSum_eq_weightedSupplyPrimeTriples] using
    weighted_prime_lower_bound_of_mangoldt c hc hmain

end Problem337

end

end OAI
