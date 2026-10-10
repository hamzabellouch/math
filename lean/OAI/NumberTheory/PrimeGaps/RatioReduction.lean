import OAI.NumberTheory.PrimeGaps.Density
import OAI.NumberTheory.PrimeGaps.RatioAlgebra

namespace OAI

namespace Problem344

theorem mem_ratioIncreaseIndices_iff_gap {n : ℕ} :
    n ∈ ratioIncreaseIndices ↔
      1 ≤ n ∧ (primeAt n : ℝ) / (n : ℝ) <
        (primeAt (n + 1) : ℝ) - (primeAt n : ℝ) := by
  constructor
  · rintro ⟨hn, hratio⟩
    exact ⟨hn, (div_lt_div_succ_iff_gap hn).1 hratio⟩
  · rintro ⟨hn, hgap⟩
    exact ⟨hn, (div_lt_div_succ_iff_gap hn).2 hgap⟩

theorem mem_ratioIncreaseIndices_of_mem_largeGapIndices {C : ℝ} {n : ℕ}
    (hbound : (primeAt n : ℝ) / (n : ℝ) ≤ C * Real.log (primeAt n : ℝ))
    (hgap : n ∈ largeGapIndices C) : n ∈ ratioIncreaseIndices := by
  apply mem_ratioIncreaseIndices_iff_gap.2
  exact ⟨hgap.1, lt_of_le_of_lt hbound hgap.2⟩

theorem eventually_largeGapIndices_subset_ratioIncreaseIndices {C : ℝ}
    (hbound : ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      (primeAt n : ℝ) / (n : ℝ) ≤ C * Real.log (primeAt n : ℝ)) :
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      n ∈ largeGapIndices C → n ∈ ratioIncreaseIndices := by
  obtain ⟨N0, hN0⟩ := hbound
  exact ⟨N0, fun n hn => mem_ratioIncreaseIndices_of_mem_largeGapIndices (hN0 n hn)⟩

end Problem344

end OAI
