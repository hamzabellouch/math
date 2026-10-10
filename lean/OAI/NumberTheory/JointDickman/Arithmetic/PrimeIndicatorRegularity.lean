import OAI.NumberTheory.JointDickman.Arithmetic.PrimeIndicatorViolations

namespace OAI

/-! # Uniform regularity loss for independent prime indicators -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem bernoulli_prefix_violation_sum (B L : ℕ) (q : ℕ → ℝ) (τ s : ℝ) {D : ℝ}
    (hP : 6 ≤ auxiliaryCutoff B) (hD : 0 ≤ D)
    (hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1)
    (herr : (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D)
    (hs : 0 < s) (he : Real.exp s ≤ 2) (hen : Real.exp (-s) ≤ 2) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      prefixViolationMass B L τ S (bernoulliSubsetMass (auxiliaryPrimes B) q S)) ≤
        Real.exp D * prefixGridError B L 4 τ s := by
  classical
  unfold prefixViolationMass
  rw [sum_comm]
  unfold prefixGridError
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  simp only [sum_add_distrib, mul_add]
  exact add_le_add (bernoulli_prefix_lower_bound B q ((i : ℝ) / L) τ s hP hD hq herr hs hen)
    (bernoulli_prefix_upper_bound B q ((i : ℝ) / L) τ s hP hD hq herr hs he)

theorem bernoulli_tail_violation_sum (B : ℕ) (q : ℕ → ℝ) (C : ℝ) {D : ℝ}
    (hP : 6 ≤ auxiliaryCutoff B) (hD : 0 ≤ D)
    (hlog : 1 ≤ Real.log (auxiliaryCutoff B)) (hC : 0 ≤ C)
    (hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1)
    (herr : (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      tailViolationMass B C S (bernoulliSubsetMass (auxiliaryPrimes B) q S)) ≤
        Real.exp D * (∑ i ∈ activeTailIndices B, tailChernoffFactor B i 4 C) := by
  classical
  simp_rw [tailViolationMass_eq_restricted _ _ hC hlog]
  rw [sum_comm, mul_sum]
  exact sum_le_sum (fun i _ => bernoulli_tail_violation_bound B i q C hP hD hq herr)

open Classical in
noncomputable def primeRegularityFailureProbability (B L : ℕ) (τ C : ℝ) (q : ℕ → ℝ) : ℝ :=
  ∑ S ∈ (auxiliaryPrimes B).powerset,
    if RegularPrimeSet B L τ C S then 0 else bernoulliSubsetMass (auxiliaryPrimes B) q S

theorem bernoulli_regularity_failure_bound (B L : ℕ) (q : ℕ → ℝ) (τ s C : ℝ) {D : ℝ}
    (hP : 6 ≤ auxiliaryCutoff B) (hD : 0 ≤ D)
    (hlog : 1 ≤ Real.log (auxiliaryCutoff B)) (hC : 0 ≤ C)
    (hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1)
    (herr : (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D)
    (hs : 0 < s) (he : Real.exp s ≤ 2) (hen : Real.exp (-s) ≤ 2) :
    primeRegularityFailureProbability B L τ C q ≤
      Real.exp D * (prefixGridError B L 4 τ s +
        ∑ i ∈ activeTailIndices B, tailChernoffFactor B i 4 C) := by
  classical
  have hpoint : primeRegularityFailureProbability B L τ C q ≤
      (∑ S ∈ (auxiliaryPrimes B).powerset,
        prefixViolationMass B L τ S (bernoulliSubsetMass (auxiliaryPrimes B) q S)) +
      (∑ S ∈ (auxiliaryPrimes B).powerset,
        tailViolationMass B C S (bernoulliSubsetMass (auxiliaryPrimes B) q S)) := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro S hS
    have hw := bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq
    split_ifs with hreg
    · exact add_nonneg (prefixViolationMass_nonneg B L τ S hw) (tailViolationMass_nonneg B C S hw)
    · exact regularity_failure_union_bound S hC hlog hw hreg
  have hp := bernoulli_prefix_violation_sum B L q τ s hP hD hq herr hs he hen
  have ht := bernoulli_tail_violation_sum B q C hP hD hlog hC hq herr
  simpa only [mul_add] using hpoint.trans (add_le_add hp ht)

/-- The probability version of manuscript (9), uniform over all proper
independent parameters with bounded total deviation from 1/(2p). -/
theorem independent_prime_regularity_loss
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {D : ℝ} (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (q : ℕ → ℝ) (C : ℝ), 0 ≤ C →
          (∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1) →
          (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D →
          primeRegularityFailureProbability B L τ C q ≤
            K * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  obtain ⟨Dt, hDt, htail⟩ := actual_tail_chernoff_sum hM (by norm_num : (0 : ℝ) < 4) (by norm_num)
  let K := Real.exp D * (Dt + 1)
  refine ⟨K, mul_pos (Real.exp_pos _) (by linarith only [hDt]), ?_⟩
  intro L τ hL hτ
  obtain ⟨s, hs, _hs1, he, hen, hprefix⟩ := prefixGridError_tendsto hM hτ
  refine ⟨fun B => prefixGridError B L 4 τ s, fun B => prefixGridError_nonneg ..,
    hprefix L 4 hL (by norm_num) (by norm_num), ?_⟩
  have hloglarge : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually_ge_atTop 1
  filter_upwards [htail, hloglarge, auxiliaryCutoff_tendsto.eventually_ge_atTop 6] with B ht hlog hP
  intro q C hC hq herr
  have hb := bernoulli_regularity_failure_bound B L q τ s C hP hD hlog hC hq herr hs he hen
  have ht' := ht (activeTailIndices B) C (fun i hi => (mem_filter.mp hi).2.le)
  have hbase := prefixGridError_nonneg B L 4 τ s
  have hexp := (Real.exp_pos (-(1 / 10 : ℝ) * C)).le
  calc
    _ ≤ Real.exp D * (prefixGridError B L 4 τ s + Dt * Real.exp (-(1 / 10 : ℝ) * C)) :=
      hb.trans (mul_le_mul_of_nonneg_left (add_le_add_right ht' _) (Real.exp_pos _).le)
    _ ≤ K * (prefixGridError B L 4 τ s + Real.exp (-(1 / 10 : ℝ) * C)) := by
      dsimp only [K]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos D).le
      nlinarith only [mul_nonneg hDt.le hbase, hexp]

end JointDickman

end OAI
