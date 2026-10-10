import OAI.NumberTheory.JointDickman.Counting.FirstCoefficientAverage
import OAI.NumberTheory.JointDickman.Probability.RegularOrientedSplit

namespace OAI

/-! # The first-recipient contribution to the amplification second moment -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- The first-recipient orientations, summed over all dyadic change scales,
have probability O_C(B^{-2}) in the actual two-site split law. -/
theorem first_oriented_probability_sum
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (L T : ℕ) (τ C : ℝ) (S : Finset ℕ),
      0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      (∀ i ∈ S, primeTailEndpoint B i ≤ 8 * B) →
      (∑ i ∈ S, twoSiteSplitProbability (auxiliaryPrimes B)
        (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) false)) ≤
      K * (2 : ℝ)^(4 * C) / (B : ℝ)^2 := by
  obtain ⟨K, hK, hk⟩ := regular_oriented_scale_sum hFord hM (16 / 5)
  obtain ⟨M, hM0, hm⟩ := coefficient_size_ratio_event_bound hFord hM
  refine ⟨K * M, mul_pos hK hM0, ?_⟩
  filter_upwards [hk, hm, amplificationCoefficientPairs_size, eventually_gt_atTop 0]
    with B hkb hmb hsize hB
  intro L T τ C S hT hTsize hcap
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hpoint : ∀ A ⊆ auxiliaryPrimes B, ∀ D ⊆ auxiliaryPrimes B,
      firstCoefficientGood B L T τ C A D →
      (∑ i ∈ S, orientedSplitMass B A D (primeTailEndpoint B i) C T) ≤
        K * (2 : ℝ)^(4 * C) / B := by
    intro A hA D hD hg
    exact hkb A D L S τ C T hA hD (hsize T _ _ hT hTsize hg.1).1
      hg.2.1 hg.2.2 hcap hT0
  have hmass : (∑ ac ∈ amplificationCoefficientPairs B T,
      primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) ≤ M / B := by
    apply (le_div_iff₀ hB0).mpr
    nlinarith only [hmb T hT hTsize]
  have hkn : 0 ≤ K * (2 : ℝ)^(4 * C) / B := by positivity
  calc
    _ ≤ ∑ i ∈ S, firstCoefficientAverage B L T τ C
        (fun A D => orientedSplitMass B A D (primeTailEndpoint B i) C T) :=
      sum_le_sum (fun i _ => oriented_probability_bound hB)
    _ = firstCoefficientAverage B L T τ C
        (fun A D => ∑ i ∈ S, orientedSplitMass B A D (primeTailEndpoint B i) C T) :=
      firstCoefficientAverage_sum B L T τ C S _
    _ ≤ (K * (2 : ℝ)^(4 * C) / B) *
        ∑ ac ∈ amplificationCoefficientPairs B T,
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
            primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2 :=
      firstCoefficientAverage_le hkn _ hpoint
    _ ≤ (K * (2 : ℝ)^(4 * C) / B) * (M / B) := mul_le_mul_of_nonneg_left hmass hkn
    _ = _ := by ring

end JointDickman

end OAI
