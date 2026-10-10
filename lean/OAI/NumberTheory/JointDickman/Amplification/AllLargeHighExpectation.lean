import OAI.NumberTheory.JointDickman.Amplification.LargeCardinalityPartition
import OAI.NumberTheory.JointDickman.Amplification.LargeAlternativeExpectation

namespace OAI

/-! # Exact cardinality-class decomposition in the tilted expectation -/

namespace JointDickman
open Finset Classical

noncomputable def tiltedAllLargeHighPairCount (B L k j : ℕ) (τ C Δ : ℝ)
    (A D V : Finset ℕ) : ℝ :=
  ∑ U ∈ (auxiliaryPrimes B \ A).powerset,
    bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U *
      if RegularPrimeSet B L τ C U then
        ((allLargeHighAlternativePairs B L k j τ C Δ A U D V).card : ℝ) else 0

theorem tiltedAllLargeHighPairCount_eq_sum {B L k j : ℕ} {τ C Δ : ℝ}
    (A D V : Finset ℕ) (hk : k ∈ Icc 1 L)
    (hτ : τ ≤ 1/2) (hℓ : 0 ≤ auxiliaryLogLength B)
    (hV : RegularPrimeSet B L τ C V) :
    tiltedAllLargeHighPairCount B L k j τ C Δ A D V =
      ∑ d ∈ range (⌊auxiliaryLogLength B⌋₊+1), ∑ f ∈ range (⌊auxiliaryLogLength B⌋₊+1),
        tiltedLargeHighPairCount B L k j d f τ C Δ A D V := by
  unfold tiltedAllLargeHighPairCount tiltedLargeHighPairCount
  calc
    _ = ∑ U ∈ (auxiliaryPrimes B \ A).powerset,
        ∑ d ∈ range (⌊auxiliaryLogLength B⌋₊+1), ∑ f ∈ range (⌊auxiliaryLogLength B⌋₊+1),
          bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U *
            if RegularPrimeSet B L τ C U then
              ((largeHighAlternativePairs B L k j d f τ C Δ A U D V).card : ℝ) else 0 := by
      apply sum_congr rfl
      intro U _
      by_cases hU : RegularPrimeSet B L τ C U
      · simp only [hU,ite_true,← mul_sum]
        have hc : ((allLargeHighAlternativePairs B L k j τ C Δ A U D V).card : ℝ) =
            ∑ d ∈ range (⌊auxiliaryLogLength B⌋₊+1), ∑ f ∈ range (⌊auxiliaryLogLength B⌋₊+1),
              ((largeHighAlternativePairs B L k j d f τ C Δ A U D V).card : ℝ) := by
          exact_mod_cast allLargeHighAlternativePairs_card A U D V hk hτ hℓ hU hV
        rw [hc]
      · simp [hU]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      rw [sum_comm]

end JointDickman

end OAI
