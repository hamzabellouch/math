import OAI.NumberTheory.JointDickman.Amplification.NoChangeProbability

namespace OAI

/-! # The integrated no-change contribution is O(B^{-2}) -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem no_change_probability_small
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ C : ℝ), ∀ᶠ B : ℕ in atTop,
      ∀ T : ℕ, 0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      twoSiteSplitProbability (auxiliaryPrimes B)
        (fun x => bothAmplificationSplitsGood B L T τ C x ∧ twoSiteNoChange x) ≤ K / (B : ℝ)^2 := by
  obtain ⟨M, hM0, hm⟩ := coefficient_size_ratio_event_bound hFord hM
  refine ⟨M, hM0, ?_⟩
  intro L τ C
  filter_upwards [hm, regular_no_change_vanishing L τ C 1 (by norm_num), eventually_gt_atTop 1]
    with B hmb hnb hB
  intro T hT hTsize
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hp : ∀ A ⊆ auxiliaryPrimes B, ∀ D ⊆ auxiliaryPrimes B,
      firstCoefficientGood B L T τ C A D → noChangeSplitMass B A D C ≤ 1 / B := by
    intro A hA D hD hg
    apply (le_div_iff₀ hB0).mpr
    nlinarith only [hnb A D hA hD hg.2.1 hg.2.2]
  have hmass : (∑ ac ∈ amplificationCoefficientPairs B T,
      primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) ≤ M / B := by
    apply (le_div_iff₀ hB0).mpr
    nlinarith only [hmb T hT hTsize]
  calc
    _ ≤ firstCoefficientAverage B L T τ C (fun A D => noChangeSplitMass B A D C) :=
      no_change_probability_bound hB
    _ ≤ (1 / (B : ℝ)) * ∑ ac ∈ amplificationCoefficientPairs B T,
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2 :=
      firstCoefficientAverage_le (by positivity) _ hp
    _ ≤ (1 / (B : ℝ)) * (M / B) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
