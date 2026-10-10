import OAI.NumberTheory.PrimeGaps.RatioReduction
import OAI.NumberTheory.PrimeGaps.PrimeGrowth
import OAI.NumberTheory.PrimeGaps.DensityBounds
import OAI.NumberTheory.PrimeGaps.DensityTransport

namespace OAI

namespace Problem344

theorem eventually_largeGapIndices_explicit_subset_ratioIncreaseIndices :
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      n ∈ largeGapIndices (2 / Real.log 2) → n ∈ ratioIncreaseIndices := by
  apply eventually_largeGapIndices_subset_ratioIncreaseIndices
  apply Filter.eventually_atTop.mp
  simpa only [primeAt] using PrimeGrowth.eventually_nth_prime_ratio_le_log

theorem positive_lower_density_prime_ratio_increases_of_explicit_large_gaps
    (hgap : ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      c * (N : ℝ) ≤ (initialCount (largeGapIndices (2 / Real.log 2)) N : ℝ)) :
    0 < lowerAsymptoticDensity ratioIncreaseIndices := by
  apply positive_lowerAsymptoticDensity_of_linear_count
  exact positive_linear_count_of_eventual_subset
    eventually_largeGapIndices_explicit_subset_ratioIncreaseIndices hgap

theorem positive_lower_density_prime_ratio_increases_of_large_gaps
    (hgap : ∀ C : ℝ, 0 < C → ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N →
        c * (N : ℝ) ≤ (initialCount (largeGapIndices C) N : ℝ)) :
    0 < lowerAsymptoticDensity ratioIncreaseIndices := by
  apply positive_lower_density_prime_ratio_increases_of_explicit_large_gaps
  exact hgap (2 / Real.log 2) (div_pos (by norm_num) (Real.log_pos (by norm_num)))

end Problem344

end OAI
