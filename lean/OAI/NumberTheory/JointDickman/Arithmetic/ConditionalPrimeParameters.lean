import OAI.NumberTheory.JointDickman.Arithmetic.PrimeIndicatorRegularity
import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryOdds

namespace OAI

/-! # The actual remaining-prime parameters after a coefficient is selected -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def remainingPrimeParameter (S : Finset ℕ) (p : ℕ) : ℝ :=
  if p ∈ S then 0 else 1 / (2 * (p : ℝ) - 1)

theorem remainingPrimeParameter_mem_Icc (S : Finset ℕ) {p : ℕ} (hp : 2 ≤ p) :
    0 ≤ remainingPrimeParameter S p ∧ remainingPrimeParameter S p ≤ 1 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold remainingPrimeParameter
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · refine ⟨div_nonneg (by norm_num) (by linarith), ?_⟩
    exact (div_le_one (by linarith : 0 < 2 * (p : ℝ) - 1)).mpr (by linarith)

theorem unselected_parameter_error {p : ℕ} (hp : 2 ≤ p) :
    |1 / (2 * (p : ℝ) - 1) - (1 / 2 : ℝ) / p| ≤ 1 / (p : ℝ)^2 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hd : 0 < 2 * (p : ℝ) - 1 := by linarith
  have heq : 1 / (2 * (p : ℝ) - 1) - (1 / 2 : ℝ) / p =
      1 / (2 * (p : ℝ) * (2 * p - 1)) := by
    field_simp
    ring
  rw [heq, abs_of_nonneg (by positivity)]
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (p : ℝ)^2)
  nlinarith only [hp']

theorem remaining_parameter_total_error {P S : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) :
    (∑ p ∈ P, |remainingPrimeParameter S p - (1 / 2 : ℝ) / p|) ≤
      1 + ∑ p ∈ S, 1 / (p : ℝ) := by
  classical
  have hpoint (p : ℕ) (hp : p ∈ P) :
      |remainingPrimeParameter S p - (1 / 2 : ℝ) / p| ≤
        1 / (p : ℝ)^2 + if p ∈ S then 1 / (p : ℝ) else 0 := by
    by_cases hs : p ∈ S
    · have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
      simp only [remainingPrimeParameter, hs, ite_true, zero_sub, abs_neg,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) / p)]
      have hh : (1 / 2 : ℝ) / p ≤ 1 / (p : ℝ) :=
        div_le_div_of_nonneg_right (by norm_num) hp0.le
      linarith [show (0 : ℝ) ≤ 1 / (p : ℝ)^2 by positivity]
    · simpa only [remainingPrimeParameter, hs, ite_false, add_zero] using
        unselected_parameter_error (hP p hp).two_le
  have hsum := sum_le_sum hpoint
  have heq : P.filter (fun p => p ∈ S) = S := by
    ext p
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hsq : (∑ p ∈ P, 1 / (p : ℝ)^2) ≤ 1 := by
    simpa using sum_reciprocal_square_tail P (by norm_num : (1 : ℕ) ≠ 0) (fun p hp => (hP p hp).one_lt)
  rw [sum_add_distrib, ← sum_filter, heq] at hsum
  exact hsum.trans (add_le_add_left hsq _)

/-- Omitting a coefficient of fixed exponential size costs o(1) in total
reciprocal prime mass, uniformly in the coefficient. -/
theorem auxiliary_selected_reciprocal_sum_small {κ : ℝ} (_hκ : 0 < κ) :
    ∀ᶠ B : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ auxiliaryPrimes B →
      (∏ p ∈ S, p : ℕ) ≤ Real.exp (κ * B) → (∑ p ∈ S, 1 / (p : ℝ)) ≤ 1 := by
  have ht : Tendsto (fun B : ℕ => (κ / Real.log 2) *
      ((B : ℝ) / (auxiliaryCutoff B : ℝ))) atTop (𝓝 0) := by
    have hp := ((polynomial_div_primeCutoff_tendsto_zero (k := 1) (by norm_num)).comp
      tendsto_natCast_atTop_atTop).const_mul (κ / Real.log 2)
    simpa only [Function.comp_def, auxiliaryCutoff, Nat.cast_pow, pow_one, mul_zero] using hp
  filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hsmall hB
  intro S hS hn
  have hP0 : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast (pow_pos (Nat.zero_lt_of_lt hB) 1000)
  have hprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (mem_filter.mp (hS hp)).1).2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (S.card : ℝ) ≤ κ * B / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    refine (selectedPrime_card_log_bound S hprime).trans ?_
    have hn0 : (0 : ℝ) < (∏ p ∈ S, p : ℕ) := by
      exact_mod_cast prod_pos (fun p hp => (hprime p hp).pos)
    simpa only [Real.log_exp] using Real.log_le_log hn0 hn
  calc
    _ ≤ ∑ _p ∈ S, 1 / (auxiliaryCutoff B : ℝ) := sum_le_sum (fun p hp =>
      one_div_le_one_div_of_le hP0 (mem_filter.mp (hS hp)).2.le)
    _ = (S.card : ℝ) / auxiliaryCutoff B := by simp [div_eq_mul_inv]
    _ ≤ (κ * B / Real.log 2) / auxiliaryCutoff B := div_le_div_of_nonneg_right hcard hP0.le
    _ = (κ / Real.log 2) * ((B : ℝ) / (auxiliaryCutoff B : ℝ)) := by ring
    _ ≤ 1 := hsmall.le

/-- Uniform regularity of the remaining indicators after any selected
coefficient in the fixed exponential range. -/
theorem remaining_prime_regularity_loss
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {κ : ℝ} (hκ : 0 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (S : Finset ℕ) (C : ℝ), 0 ≤ C → S ⊆ auxiliaryPrimes B →
          (∏ p ∈ S, p : ℕ) ≤ Real.exp (κ * B) →
          primeRegularityFailureProbability B L τ C (remainingPrimeParameter S) ≤
            K * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  obtain ⟨K, hK, hbound⟩ := independent_prime_regularity_loss hM (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨K, hK, ?_⟩
  intro L τ hL hτ
  obtain ⟨ε, hε, hlim, hevent⟩ := hbound L τ hL hτ
  refine ⟨ε, hε, hlim, ?_⟩
  filter_upwards [hevent, auxiliary_selected_reciprocal_sum_small hκ] with B hB hsmall
  intro S C hC hS hn
  have hprime : ∀ p ∈ auxiliaryPrimes B, p.Prime :=
    fun p hp => (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  apply hB (remainingPrimeParameter S) C hC
  · exact fun p hp => remainingPrimeParameter_mem_Icc S (hprime p hp).two_le
  · exact (remaining_parameter_total_error hprime hS).trans (by linarith only [hsmall S hS hn])

end JointDickman

end OAI
