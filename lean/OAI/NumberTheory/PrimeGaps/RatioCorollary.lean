import OAI.NumberTheory.PrimeGaps.Main
import OAI.NumberTheory.PrimeGaps.RatioDensity

namespace OAI

namespace Problem344

private theorem largeGap_count_eq (C : ℝ) (N : ℕ) :
    initialCount (largeGapIndices C) N =
      (LargePrimeGaps.largeGapIndices C N).card := by
  classical
  unfold initialCount LargePrimeGaps.largeGapIndices
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  simp only [largeGapIndices, Set.mem_ofPred_eq, primeAt,
    LargePrimeGaps.prime, hn1, true_and]

theorem positive_lower_density_prime_ratio_increases :
    0 < lowerAsymptoticDensity ratioIncreaseIndices := by
  apply positive_lower_density_prime_ratio_increases_of_large_gaps
  intro C hC
  rcases LargePrimeGaps.main C hC with ⟨c, hc, N0, hN0⟩
  refine ⟨c, hc, N0, ?_⟩
  intro N hN
  rw [largeGap_count_eq]
  exact hN0 N hN

theorem large_gaps_and_ratio_density :
    (∀ C : ℝ, 0 < C →
      ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        c * (N : ℝ) ≤ ((LargePrimeGaps.largeGapIndices C N).card : ℝ)) ∧
    0 < lowerAsymptoticDensity ratioIncreaseIndices :=
  ⟨LargePrimeGaps.main, positive_lower_density_prime_ratio_increases⟩

end Problem344

end OAI
