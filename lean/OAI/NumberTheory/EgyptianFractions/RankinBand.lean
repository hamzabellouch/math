import OAI.NumberTheory.EgyptianFractions.SmoothRankinBounds
import OAI.NumberTheory.EgyptianFractions.PrimeReciprocalSharp

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- Smooth harmonic divisor tails with all Euler and prime sums evaluated. -/
theorem uniform_divisor_smooth_rankin_loglog_bound (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β V W : ℝ, 0 ≤ β → β ≤ 1 / 4 → 1 ≤ W →
      ∀ N : ℕ, (∀ p ∈ N.primesBelow, (p : ℝ) ≤ Real.exp W) → ∀ s : Finset ℕ,
      (∀ n ∈ s, n ∈ N.smoothNumbers) →
      (∀ n ∈ s, Real.exp V ≤ (n : ℝ)) →
      (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
        Real.exp (-β * V + C * Real.exp (β * W) * Real.log (1 + W)) := by
  obtain ⟨C, hC, hbound⟩ := uniform_divisor_smooth_rankin_bound r
  refine ⟨C * Real.exp 1, by positivity, ?_⟩
  intro β V W hβ hβquarter hW N hN s hs hlarge
  have hT : 2 ≤ Real.exp W := by
    have := Real.add_one_le_exp W
    linarith
  have hprime := prime_weighted_reciprocal_sum_le N.primesBelow (Real.exp W) β hT hβ
    (fun p hp => Nat.prime_of_mem_primesBelow hp)
    hN
  rw [Real.log_exp, ← Real.exp_mul] at hprime
  simp only [show -1 + β = β - 1 by ring, mul_comm W β] at hprime
  refine (hbound β V hβ hβquarter N s hs hlarge).trans (Real.exp_le_exp.mpr ?_)
  have h := mul_le_mul_of_nonneg_left hprime hC.le
  nlinarith

/-- The exact intermediate-prime-band Rankin estimate. The only scale
restriction is the explicit admissibility of the chosen Rankin exponent. -/
theorem divisor_rankin_intermediate_band (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v t : ℝ, 1 ≤ t → t ≤ v →
      Real.log (v / t) / (10 * t) ≤ 1 / 4 →
      ∀ N : ℕ, (∀ p ∈ N.primesBelow, (p : ℝ) ≤ Real.exp (2 * t)) → ∀ s : Finset ℕ,
      (∀ n ∈ s, n ∈ N.smoothNumbers) →
      (∀ n ∈ s, Real.exp (v / 5) ≤ (n : ℝ)) →
      (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
        Real.exp (-(v / t) * Real.log (v / t) / 50 +
          C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t)) := by
  obtain ⟨C, hC, hbound⟩ := uniform_divisor_smooth_rankin_loglog_bound r
  refine ⟨2 * C, by positivity, ?_⟩
  intro v t ht htv hβquarter N hN s hs hlarge
  have htpos : 0 < t := by linarith
  have hvpos : 0 < v := by linarith
  have hQ : 1 ≤ v / t := (one_le_div htpos).mpr htv
  have hβ : 0 ≤ Real.log (v / t) / (10 * t) :=
    div_nonneg (Real.log_nonneg hQ) (by positivity)
  have h := hbound (Real.log (v / t) / (10 * t)) (v / 5) (2 * t)
    hβ hβquarter (by linarith) N hN s hs hlarge
  rw [rankin_band_negative_exponent (ne_of_gt htpos),
    rankin_band_positive_exponent htpos hvpos] at h
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have hlog := mul_le_mul_of_nonneg_left (log_one_add_two_mul_le t ht)
    (mul_nonneg hC.le (Real.rpow_nonneg (le_of_lt (div_pos hvpos htpos)) (1 / 5 : ℝ)))
  nlinarith

/-- A real-cutoff version avoiding any rounding obligation at the call site. -/
theorem divisor_rankin_intermediate_band_of_prime_divisors (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v t : ℝ, 1 ≤ t → t ≤ v →
      Real.log (v / t) / (10 * t) ≤ 1 / 4 →
      ∀ s : Finset ℕ,
      (∀ n ∈ s, ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ Real.exp (2 * t)) →
      (∀ n ∈ s, Real.exp (v / 5) ≤ (n : ℝ)) →
      (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
        Real.exp (-(v / t) * Real.log (v / t) / 50 +
          C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t)) := by
  obtain ⟨C, hC, hbound⟩ := divisor_rankin_intermediate_band r
  refine ⟨C, hC, ?_⟩
  intro v t ht htv hβ s hprimes hlarge
  let N : ℕ := ⌊Real.exp (2 * t)⌋₊ + 1
  have hcap : ∀ p ∈ N.primesBelow, (p : ℝ) ≤ Real.exp (2 * t) := by
    intro p hp
    have hpN := Nat.lt_of_mem_primesBelow hp
    have hpfloor : p ≤ ⌊Real.exp (2 * t)⌋₊ := by dsimp [N] at hpN; omega
    exact (show (p : ℝ) ≤ (⌊Real.exp (2 * t)⌋₊ : ℕ) by exact_mod_cast hpfloor).trans
      (Nat.floor_le (le_of_lt (Real.exp_pos _)))
  have hsmooth : ∀ n ∈ s, n ∈ N.smoothNumbers := by
    intro n hn
    apply Nat.mem_smoothNumbers'.mpr
    intro p hp hpn
    exact Nat.lt_succ_of_le (Nat.le_floor (hprimes n hn p hp hpn))
  exact hbound v t ht htv hβ N hcap s hsmooth hlarge

end Problem337

end

end OAI
