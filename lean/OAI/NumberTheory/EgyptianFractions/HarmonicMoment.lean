import OAI.NumberTheory.EgyptianFractions.FiniteEulerBound
import OAI.NumberTheory.EgyptianFractions.DivisorLocalFactor
import OAI.NumberTheory.EgyptianFractions.PrimeReciprocalBound

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.DivisorMoment

/-- Finite Euler products combine uniform local control with a prime reciprocal bound. -/
theorem harmonic_divisor_moment_of_local_and_primes (r : ℕ) (C B : ℝ)
    (hC : 0 < C) (hB : 0 < B)
    (hlocal : ∀ p : ℕ, p.Prime → ∀ L : ℕ,
      Real.log (∑ j ∈ Finset.range (L + 1),
        (j + 1 : ℝ) ^ r * ((p : ℝ)⁻¹) ^ j) ≤ C / p)
    (hprimes : ∀ T : ℕ, 2 ≤ T →
      (∑ p ∈ T.factorial.primeFactors, (1 : ℝ) / p) ≤
        B * Real.log (1 + Real.log (T : ℝ))) :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℕ, 2 ≤ T →
      (∑ n ∈ Finset.Icc 1 T, (n.divisors.card : ℝ) ^ r / n) ≤
        Real.exp (A * Real.log (1 + Real.log (T : ℝ))) := by
  refine ⟨C * B, mul_pos hC hB, ?_⟩
  intro T hT
  have heuler := divisor_moment_sum_le_exp r T 1 C (by
    intro p hp hpT L
    simpa only [Real.rpow_neg_one, div_eq_mul_inv] using hlocal p hp L)
  have hprime := mul_le_mul_of_nonneg_left (hprimes T hT) hC.le
  have hfinal := heuler.trans (Real.exp_le_exp.mpr (by
    simpa only [Real.rpow_neg_one, one_div] using hprime))
  simpa only [Real.rpow_neg_one, div_eq_mul_inv, mul_assoc] using hfinal

/-- The prime factors of a factorial are exactly the primes up to its index. -/
theorem factorial_primeFactors_eq_primesLE (T : ℕ) :
    T.factorial.primeFactors = Nat.primesLE T := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpprime, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpprime.dvd_factorial.mp hpdvd, hpprime⟩
  · intro hp
    obtain ⟨hpT, hpprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primeFactors.mpr
      ⟨hpprime, hpprime.dvd_factorial.mpr hpT, Nat.factorial_ne_zero T⟩

/-- An unconditional harmonic divisor-moment bound, with a constant depending only on r. -/
theorem harmonic_divisor_moment_bound (r : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℕ, 2 ≤ T →
      (∑ n ∈ Finset.Icc 1 T, (n.divisors.card : ℝ) ^ r / n) ≤
        Real.exp (A * Real.log (1 + Real.log (T : ℝ))) := by
  obtain ⟨C, hC, hfactor⟩ := divisor_full_local_factor_bound (r : ℝ)
  apply harmonic_divisor_moment_of_local_and_primes r C 56 hC (by norm_num)
  · intro p hp L
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have h := (hfactor (p : ℝ) 1 hpR (by norm_num)).2.2 L
    simpa only [Real.rpow_natCast, Real.rpow_neg_one, div_eq_mul_inv] using h
  · intro T hT
    rw [factorial_primeFactors_eq_primesLE]
    exact Problem337.sum_prime_reciprocals_le_loglog T hT

/-- Arbitrary real moments follow by increasing the moment to a natural number. -/
theorem harmonic_divisor_real_moment_bound (r : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℕ, 2 ≤ T →
      (∑ n ∈ Finset.Icc 1 T, (n.divisors.card : ℝ) ^ r / n) ≤
        Real.exp (A * Real.log (1 + Real.log (T : ℝ))) := by
  obtain ⟨A, hA, hbound⟩ := harmonic_divisor_moment_bound ⌈r⌉₊
  refine ⟨A, hA, ?_⟩
  intro T hT
  apply le_trans _ (hbound T hT)
  apply Finset.sum_le_sum
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  have hcard : 1 ≤ n.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (Nat.ne_of_gt hnpos)⟩
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hcard) (Nat.le_ceil r)

/-- Real cutoffs are allowed, as in the uniform divisor-moment estimate. -/
theorem harmonic_divisor_moment_real_cutoff (r : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ X : ℝ, 2 ≤ X →
      (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (n.divisors.card : ℝ) ^ r / n) ≤
        Real.exp (A * Real.log (1 + Real.log X)) := by
  obtain ⟨A, hA, hbound⟩ := harmonic_divisor_real_moment_bound r
  refine ⟨A, hA, ?_⟩
  intro X hX
  have hfloor : 2 ≤ ⌊X⌋₊ := Nat.le_floor hX
  apply (hbound ⌊X⌋₊ hfloor).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hA.le
  have hfloorR : (2 : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast hfloor
  have hlognonneg : 0 ≤ Real.log (⌊X⌋₊ : ℝ) := Real.log_nonneg (by linarith)
  apply Real.log_le_log (by linarith)
  have hlogs := Real.log_le_log (by linarith : (0 : ℝ) < ⌊X⌋₊)
    (Nat.floor_le (by linarith : 0 ≤ X))
  linarith

end Problem337.DivisorMoment

end

end OAI
