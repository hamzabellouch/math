import OAI.NumberTheory.JointDickman.Amplification.SingleViolationSums
import OAI.NumberTheory.JointDickman.Counting.CoefficientRegularityLoss

namespace OAI

/-! # The one-weight regularity-loss estimate -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficient_truncation_loss_bound (B L n : ℕ) (τ C : ℝ)
    (hC : 0 ≤ C) (hlog : 1 ≤ Real.log (auxiliaryCutoff B)) :
    coefficientWeight B n - regularCoefficientWeight B L τ C n ≤
      prefixViolationMass B L τ (coefficientPrimeSet B n) (coefficientWeight B n) +
      tailViolationMass B C (coefficientPrimeSet B n) (coefficientWeight B n) := by
  have hw := coefficientWeight_nonneg B n
  unfold regularCoefficientWeight
  split_ifs with hreg
  · simpa only [sub_self] using add_nonneg
      (prefixViolationMass_nonneg B L τ (coefficientPrimeSet B n) hw)
      (tailViolationMass_nonneg B C (coefficientPrimeSet B n) hw)
  · simpa only [sub_zero] using regularity_failure_union_bound (coefficientPrimeSet B n) hC hlog hw hreg

/-- The first-moment version of manuscript (9), with an error sequence
independent of the interval and the tail cutoff. -/
theorem single_coefficient_regularity_loss
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {δ : ℝ} (hδ : 0 < δ) (hδ32 : δ ≤ 32) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (u v : ℕ), 0 ≤ C → u ≤ v →
          Real.exp (δ * B) ≤ (v : ℝ) - u →
          (∑ n ∈ Ico u v, (coefficientWeight B n - regularCoefficientWeight B L τ C n)) ≤
            K * ((v : ℝ) - u) * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  obtain ⟨Cp, hCp, hp⟩ := single_prefix_sum_bound hFord hM hδ
  obtain ⟨Ct, hCt, ht⟩ := single_tail_sum_bound hFord hM hδ
  obtain ⟨D, hD, htail⟩ := actual_tail_chernoff_sum hM (by linarith : 0 < δ / 8)
    (by linarith : δ / 8 ≤ 4)
  let K := Cp + Ct * D + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro L τ hL hτ
  obtain ⟨s, hs, hs1, he, hen, hprefix⟩ := prefixGridError_tendsto hM hτ
  let ε := fun B => prefixGridError B L (δ / 8) τ s + regularityRemainder B L
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using (hprefix L (δ / 8) hL (by linarith) (by linarith)).add (regularityRemainder_tendsto L)
  refine ⟨ε, fun B => add_nonneg (prefixGridError_nonneg ..) (regularityRemainder_nonneg ..), hε, ?_⟩
  have hloglarge : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually_ge_atTop 1
  filter_upwards [sieveCutoff_eventually (by linarith : 0 < δ / 8), htail,
    auxiliaryLogLength_between, single_coefficient_remainder_power hδ, hloglarge,
    eventually_gt_atTop 1] with B hcut htailB hℓ hrem hlog hB
  intro C u v hC huv hlen
  let H := (v : ℝ) - u
  let E := singleCoefficientRemainder B (sieveCutoff (δ / 8) B)
  have hH : 0 ≤ H := (Real.exp_pos _).le.trans hlen
  have hpB := hp B u v hB hcut.1 hcut.2.1 (by linarith only [hcut.2.2.1]) huv
    L τ s hL hτ.le hs (by linarith only [hs1]) he hen hℓ.1 hℓ.2
  have htB := ht B u v hB hcut.1 hcut.2.1 (by linarith only [hcut.2.2.1]) huv hlog C hC
  have hmass := sum_le_sum (s := Ico u v) (fun n _ => coefficient_truncation_loss_bound B L n τ C hC hlog)
  rw [sum_add_distrib] at hmass
  have hsum := hmass.trans (add_le_add hpB htB)
  have htail' := mul_le_mul_of_nonneg_left
    (htailB (activeTailIndices B) C (fun i hi => (mem_filter.mp hi).2.le)) (mul_nonneg hCt.le hH)
  have hrem' : (2 * (L : ℝ) * B + (B : ℝ)^2) * E ≤ H * regularityRemainder B L := by
    have hh := mul_le_mul_of_nonneg_left (hrem H hlen)
      (by positivity : (0 : ℝ) ≤ 2 * (L : ℝ) * B + (B : ℝ)^2)
    simpa only [E, regularityRemainder, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
  have hCpK : Cp ≤ K := by dsimp [K]; linarith only [mul_pos hCt hD]
  have hCtK : Ct * D ≤ K := by dsimp [K]; linarith only [hCp]
  have h1K : 1 ≤ K := by dsimp [K]; linarith only [hCp, mul_pos hCt hD]
  have hp' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCpK hH)
    (prefixGridError_nonneg B L (δ / 8) τ s)
  have ht' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCtK hH)
    (Real.exp_pos (-(1 / 10 : ℝ) * C)).le
  have hr' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1K hH)
    (regularityRemainder_nonneg B L)
  change _ ≤ K * H * (ε B + Real.exp (-(1 / 10 : ℝ) * C))
  dsimp only [H, E] at htail' hrem' hp' ht' hr'
  dsimp only [ε, H]
  nlinarith only [hsum, htail', hrem', hp', ht', hr']

end JointDickman

end OAI
