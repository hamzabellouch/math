import OAI.NumberTheory.EgyptianFractions.SmoothRankin
import OAI.NumberTheory.EgyptianFractions.DivisorLocalFactor

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- Uniform Rankin estimate for smooth harmonic divisor moments. The constant
depends only on the moment order, not on the smoothness cutoff or the tail. -/
theorem uniform_divisor_smooth_rankin_bound (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β V : ℝ, 0 ≤ β → β ≤ 1 / 4 →
      ∀ N : ℕ, ∀ s : Finset ℕ,
      (∀ n ∈ s, n ∈ N.smoothNumbers) →
      (∀ n ∈ s, Real.exp V ≤ (n : ℝ)) →
      (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
        Real.exp (-β * V + C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1)) := by
  obtain ⟨C, hC, hfactor⟩ := DivisorMoment.divisor_full_local_factor_bound (r : ℝ)
  refine ⟨C, hC, ?_⟩
  intro β V hβ hβquarter N s hs hlarge
  apply divisor_smooth_rankin_log_bound r hβ (by linarith) N s hs hlarge
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by
    exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
  have h := (hfactor (p : ℝ) (1 - β) hp2 (by linarith)).2.1
  have hexp : -(1 - β) = β - 1 := by ring
  simpa only [divisorEulerFactor, Nat.cast_add, Nat.cast_one, Real.rpow_natCast, hexp] using h

/-- Prime powers with exponent just above `-1` are estimated by prime
reciprocals, with the customary exponential loss at the smoothness scale. -/
theorem prime_rpow_sum_le_exp_mul_reciprocals {β W : ℝ} (hβ : 0 ≤ β)
    (N : ℕ) (hN : (N : ℝ) ≤ Real.exp W) :
    (∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1)) ≤
      Real.exp (β * W) * ∑ p ∈ N.primesBelow, (1 : ℝ) / (p : ℝ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).pos
  have hpN : (p : ℝ) ≤ N := by exact_mod_cast (Nat.lt_of_mem_primesBelow hp).le
  have hpow := Real.rpow_le_rpow (le_of_lt hpR) (hpN.trans hN) hβ
  rw [← Real.exp_mul] at hpow
  rw [Real.rpow_sub_one (ne_of_gt hpR)]
  have h := div_le_div_of_nonneg_right hpow (le_of_lt hpR)
  simpa only [mul_comm W β, mul_one_div] using h

/-- The smooth-prefix estimate in the form used for intermediate-prime
bands. All remaining number theory is isolated in the
prime reciprocal sum, rather than in a product over local factors. -/
theorem uniform_divisor_smooth_rankin_reciprocal_bound (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β V W : ℝ, 0 ≤ β → β ≤ 1 / 4 →
      ∀ N : ℕ, (N : ℝ) ≤ Real.exp W → ∀ s : Finset ℕ,
      (∀ n ∈ s, n ∈ N.smoothNumbers) →
      (∀ n ∈ s, Real.exp V ≤ (n : ℝ)) →
      (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
        Real.exp (-β * V + C * Real.exp (β * W) *
          ∑ p ∈ N.primesBelow, (1 : ℝ) / (p : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := uniform_divisor_smooth_rankin_bound r
  refine ⟨C, hC, ?_⟩
  intro β V W hβ hβquarter N hN s hs hlarge
  refine (hbound β V hβ hβquarter N s hs hlarge).trans (Real.exp_le_exp.mpr ?_)
  have h := mul_le_mul_of_nonneg_left (prime_rpow_sum_le_exp_mul_reciprocals hβ N hN) hC.le
  nlinarith

theorem rankin_band_negative_exponent {v t : ℝ} (ht : t ≠ 0) :
    -(Real.log (v / t) / (10 * t)) * (v / 5) =
      -(v / t) * Real.log (v / t) / 50 := by
  field_simp
  ring

theorem rankin_band_positive_exponent {v t : ℝ} (ht : 0 < t) (hv : 0 < v) :
    Real.exp ((Real.log (v / t) / (10 * t)) * (2 * t)) =
      (v / t) ^ (1 / 5 : ℝ) := by
  rw [Real.rpow_def_of_pos (div_pos hv ht)]
  congr 1
  field_simp
  ring

theorem log_one_add_two_mul_le (t : ℝ) (ht : 1 ≤ t) :
    Real.log (1 + 2 * t) ≤ 2 * Real.log (2 * t) := by
  have htpos : 0 < 2 * t := by linarith
  have hbound : 1 + 2 * t ≤ (2 * t) ^ 2 := by nlinarith
  have h := Real.log_le_log (show 0 < 1 + 2 * t by linarith) hbound
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

end Problem337

end

end OAI
