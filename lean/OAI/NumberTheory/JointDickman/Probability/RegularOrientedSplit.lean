import OAI.NumberTheory.JointDickman.Probability.OrientedSplitBound
import OAI.NumberTheory.JointDickman.Probability.HighCoinExponent
import OAI.NumberTheory.JointDickman.Amplification.DyadicChangeScales

namespace OAI

/-! # The regularity gain for one oriented change interval -/

namespace JointDickman

open Finset Filter
open scoped Topology

/-- The manuscript's conditional O_C((Y/B)^alpha/Y) estimate for a
recipient at one dyadic scale, in the actual remaining-prime law. -/
theorem regular_oriented_split_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (κ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (A D : Finset ℕ) (L i : ℕ) (τ C T : ℝ),
      A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B →
      (∏ p ∈ A, p : ℕ) ≤ Real.exp (κ * B) →
      RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D →
      0 < primeTailEndpoint B i →
      Real.log (auxiliaryCutoff B) ≤ primeTailEndpoint B i →
      primeTailEndpoint B i ≤ 8 * B → 0 < T →
      orientedSplitMass B A D (primeTailEndpoint B i) C T ≤
        K * (2 : ℝ)^(4 * C) * (primeTailEndpoint B i / B)^amplificationExponent /
          primeTailEndpoint B i := by
  obtain ⟨K, hK, hbound⟩ := oriented_split_bound hFord hM κ
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hb hB
  intro A D L i τ C T hA hD hsize hAr hDr hY hYL hYB hT
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  let Y := primeTailEndpoint B i
  let Q := upperAdditionPrimes B Y
  let k := (2 / 5 : ℝ) * Real.log ((B : ℝ) / Y) - C
  have ha : k ≤ ((A ∩ Q).card : ℝ) := by
    rw [selected_upperAdditionPrimes hA]
    exact hAr.2 i
  have hd : k ≤ ((D ∩ Q).card : ℝ) := by
    rw [selected_upperAdditionPrimes hD]
    exact hDr.2 i
  have hparam (S : Finset ℕ) : ∀ p ∈ Q,
      0 ≤ remainingPrimeParameter S p ∧ remainingPrimeParameter S p ≤ 1 :=
    fun p hp => remainingPrimeParameter_mem_Icc S (auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1).two_le
  have hx := highNoAdditionMass_nonneg Q (remainingPrimeParameter D) k (hparam D)
  have hy := highNoAdditionMass_nonneg Q (remainingPrimeParameter A) k (hparam A)
  have hxb := remaining_high_no_addition_bound Q (remainingPrimeParameter D) k (hparam D)
  have hyb := remaining_high_no_addition_bound Q (remainingPrimeParameter A) k (hparam A)
  have hfour := high_coin_four_factor_bound hB0 hY ha hd hx hy hxb hyb
  have hraw := hb A D Y C T hA hD hsize hY hYL hYB hT
  have hmul := mul_le_mul_of_nonneg_right hfour (div_nonneg hK.le hY.le)
  calc
    _ ≤ (1 / 2 : ℝ)^(A ∩ Q).card * (1 / 2 : ℝ)^(D ∩ Q).card *
        (highNoAdditionMass Q (remainingPrimeParameter D) k *
          highNoAdditionMass Q (remainingPrimeParameter A) k) * (K / Y) := by
      convert hraw using 1; ring
    _ ≤ ((2 : ℝ)^(4 * C) * (Y / B)^amplificationExponent) * (K / Y) := hmul
    _ = _ := by ring


/-- All dyadic change intervals together cost O_C(1/B), uniformly in the
first coefficient sets satisfying the stated regularity conditions. -/
theorem regular_oriented_scale_sum
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (κ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (A D : Finset ℕ) (L : ℕ) (S : Finset ℕ) (τ C T : ℝ),
      A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B →
      (∏ p ∈ A, p : ℕ) ≤ Real.exp (κ * B) →
      RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D →
      (∀ i ∈ S, primeTailEndpoint B i ≤ 8 * B) → 0 < T →
      (∑ i ∈ S, orientedSplitMass B A D (primeTailEndpoint B i) C T) ≤ K * (2 : ℝ)^(4 * C) / B := by
  obtain ⟨K, hK, hbound⟩ := regular_oriented_split_bound hFord hM κ
  let G := (8 : ℝ)^(amplificationExponent - 1) *
    ((2 : ℝ)^(amplificationExponent - 1) / ((2 : ℝ)^(amplificationExponent - 1) - 1))
  have hpow : 1 < (2 : ℝ)^(amplificationExponent - 1) :=
    Real.one_lt_rpow (by norm_num) (sub_pos.mpr amplificationExponent_gt_one)
  have hG : 0 < G := by dsimp [G]; positivity
  have hlog : Tendsto (fun B : ℕ => Real.log (auxiliaryCutoff B)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)
  refine ⟨K * G, mul_pos hK hG, ?_⟩
  filter_upwards [hbound, hlog.eventually_gt_atTop 0, eventually_gt_atTop 0] with B hb hL0 hB
  intro A D L S τ C T hA hD hsize hAr hDr hcap hT
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hY0 (i : ℕ) : 0 < primeTailEndpoint B i := mul_pos (by positivity) hL0
  have hYL (i : ℕ) : Real.log (auxiliaryCutoff B) ≤ primeTailEndpoint B i := by
    exact le_mul_of_one_le_left hL0.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hs := amplification_scale_sum S hB0 hL0 hcap
  change (∑ i ∈ S, (primeTailEndpoint B i / B)^amplificationExponent / primeTailEndpoint B i) ≤ G / B at hs
  calc
    _ ≤ ∑ i ∈ S, K * (2 : ℝ)^(4 * C) * (primeTailEndpoint B i / B)^amplificationExponent / primeTailEndpoint B i :=
      sum_le_sum (fun i hi => hb A D L i τ C T hA hD hsize hAr hDr (hY0 i) (hYL i) (hcap i hi) hT)
    _ = (K * (2 : ℝ)^(4 * C)) *
        ∑ i ∈ S, (primeTailEndpoint B i / B)^amplificationExponent / primeTailEndpoint B i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ (K * (2 : ℝ)^(4 * C)) * (G / B) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
