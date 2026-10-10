import OAI.NumberTheory.JointDickman.Amplification.FourSubsetFailure

namespace OAI

/-! # Removing all four regularity cutoffs in the amplification mass -/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- In the actual independent-site fair-split model, the B-normalized
size-and-ratio mass lost at any of the four cutoffs tends to zero, up to
the uniform exponential tail-cutoff error. -/
theorem amplification_regularity_loss
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T : ℕ), 0 ≤ C → 0 < T →
          (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
          (B : ℝ) * fairFourSubsetFailure B L T τ C ≤
            K * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  classical
  obtain ⟨Kc, hKc, hcoef⟩ := coefficient_cutoff_removal hFord hM
  obtain ⟨Kr, hKr, hremaining⟩ := fair_remaining_pair_regularity_loss hM
    (by norm_num : (0 : ℝ) < 16 / 5)
  obtain ⟨M, hM0, hmass⟩ := coefficient_size_ratio_event_bound hFord hM
  let K := Kc + M * Kr
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro L τ hL hτ
  obtain ⟨εc, hεc0, hεc, hclarge⟩ := hcoef L τ hL hτ
  obtain ⟨εr, hεr0, hεr, hrlarge⟩ := hremaining L τ hL hτ
  let ε := fun B => εc B + εr B
  refine ⟨ε, fun B => add_nonneg (hεc0 B) (hεr0 B), ?_, ?_⟩
  · simpa only [ε, add_zero] using hεc.add hεr
  filter_upwards [hclarge, hrlarge, hmass, amplificationCoefficientPairs_size,
    eventually_gt_atTop 0] with B hc hr hm hsize hB
  intro C T hC hT hTsize
  let F := εr B + Real.exp (-(1 / 10 : ℝ) * C)
  have hF : 0 ≤ F := add_nonneg (hεr0 B) (Real.exp_pos _).le
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hrem : (∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
      if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T then
        fairRemainingPairFailure B L τ C A D else 0) ≤
      (∑ ac ∈ amplificationCoefficientPairs B T,
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) * Kr * F := by
    rw [primeProductPair_sum_event]
    simp only [sum_mul]
    apply sum_le_sum
    intro A hA
    apply sum_le_sum
    intro D hD
    by_cases hp : (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T
    · simp only [hp, ite_true]
      obtain ⟨ha, hd⟩ := hsize T _ _ hT hTsize hp
      exact hr A D C hC (mem_powerset.mp hA) (mem_powerset.mp hD) ha hd
    · simp only [hp, ite_false, zero_mul, le_refl]
  have hrem' : (B : ℝ) * (∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
      if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T then
        fairRemainingPairFailure B L τ C A D else 0) ≤ M * Kr * F := by
    calc
      _ ≤ (B : ℝ) * ((∑ ac ∈ amplificationCoefficientPairs B T,
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
            primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) * Kr * F) :=
        mul_le_mul_of_nonneg_left hrem hB0
      _ = ((B : ℝ) * (∑ ac ∈ amplificationCoefficientPairs B T,
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
            primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2)) * Kr * F := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hm T hT hTsize) hKr.le) hF
  have hc' := hc C T hC hT hTsize
  have hu := mul_le_mul_of_nonneg_left (fairFourSubsetFailure_union B L T τ C) hB0
  have hx := mul_nonneg hKc.le (hεr0 B)
  have hy := mul_nonneg (mul_nonneg hM0.le hKr.le) (hεc0 B)
  dsimp only [K, ε, F] at *
  nlinarith only [hu, hc', hrem', hx, hy]

end JointDickman

end OAI
