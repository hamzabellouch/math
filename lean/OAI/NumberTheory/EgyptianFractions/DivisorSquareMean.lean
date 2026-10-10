import Mathlib

namespace OAI
/-!
# An elementary mean-square bound for the divisor function

The pointwise majorant `tau^2 ≤ zeta^4` and the elementary harmonic-sum
bound supply the coefficient energy used in finite Type-II estimates.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.zeta
open Finset ArithmeticFunction

namespace Problem337.DivisorSquareMean

lemma square_le_sigma_convolution_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (k + 1) ^ 2 ≤ (sigma 0 * sigma 0) (p ^ k) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => sigma 0 a * sigma 0 b),
    Nat.sum_divisors_prime_pow hp]
  calc
    (k + 1) ^ 2 = ∑ i ∈ range (k + 1), (k + 1) := by simp [pow_two]
    _ ≤ ∑ i ∈ range (k + 1), sigma 0 (p ^ i) * sigma 0 (p ^ k / p ^ i) := by
      apply sum_le_sum
      intro i hi
      have hik : i ≤ k := by simpa using hi
      rw [Nat.pow_div hik hp.pos,
        sigma_zero_apply_prime_pow hp, sigma_zero_apply_prime_pow hp]
      have hsub : i + (k - i) = k := Nat.add_sub_of_le hik
      nlinarith

theorem card_divisors_sq_le_convolution (n : ℕ) :
    n.divisors.card ^ 2 ≤ (sigma 0 * sigma 0) n := by
  by_cases hn : n = 0
  · simp [hn]
  have hf : IsMultiplicative (sigma 0 * sigma 0) :=
    isMultiplicative_sigma.mul isMultiplicative_sigma
  rw [Nat.card_divisors hn, ← prod_pow,
    hf.multiplicative_factorization (sigma 0 * sigma 0) hn]
  change (∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ 2) ≤
    ∏ p ∈ n.factorization.support, (sigma 0 * sigma 0) (p ^ n.factorization p)
  rw [Nat.support_factorization]
  exact prod_le_prod fun p hp =>
    square_le_sigma_convolution_prime_pow (Nat.prime_of_mem_primeFactors hp) _

theorem card_divisors_sq_le_zeta_four (n : ℕ) :
    n.divisors.card ^ 2 ≤ (ζ ^ 4) n := by
  have hs : sigma 0 = ζ * ζ := by
    rw [← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]
  convert card_divisors_sq_le_convolution n using 1
  rw [hs]
  congr 1
  ring

lemma real_harmonic_eq_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ n ∈ Ioc 0 N, (n : ℝ)⁻¹ := by
  have hset : Ioc 0 N = Icc 1 N := by
    ext n
    simp only [mem_Ioc, mem_Icc]
    omega
  simp [hset, harmonic_eq_sum_Icc]

lemma real_harmonic_nonneg (N : ℕ) : 0 ≤ (harmonic N : ℝ) := by
  rw [real_harmonic_eq_sum]
  positivity

lemma real_harmonic_mono {M N : ℕ} (h : M ≤ N) :
    (harmonic M : ℝ) ≤ (harmonic N : ℝ) := by
  rw [real_harmonic_eq_sum, real_harmonic_eq_sum]
  exact sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right h)
    (fun _ _ _ => by positivity)

/-- The summatory `(k+1)`-fold divisor function costs at most `k` harmonic factors. -/
theorem sum_zeta_pow_le_harmonic (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, (ζ ^ (k + 1)) n : ℕ) ≤
      (N : ℝ) * (harmonic N : ℝ) ^ k := by
  induction k generalizing N with
  | zero =>
    rw [Nat.zero_add, pow_one, sum_Ioc_zeta, pow_zero, mul_one]
  | succ k ih =>
    rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ',
      sum_Ioc_mul_eq_sum_sum]
    simp only [Nat.cast_sum, Nat.cast_mul]
    calc
      ∑ n ∈ Ioc 0 N, (ζ n : ℝ) *
          (∑ m ∈ Ioc 0 (N / n), ((ζ ^ (k + 1)) m : ℝ))
        ≤ ∑ n ∈ Ioc 0 N, ((N : ℝ) / n) * (harmonic N : ℝ) ^ k := by
          apply sum_le_sum
          intro n hn
          have hn0 : n ≠ 0 := (mem_Ioc.mp hn).1.ne'
          rw [zeta_apply_ne hn0, Nat.cast_one, one_mul]
          have hi := ih (N / n)
          simp only [Nat.cast_sum] at hi
          exact hi.trans (mul_le_mul Nat.cast_div_le
            (pow_le_pow_left₀ (real_harmonic_nonneg _) (real_harmonic_mono (Nat.div_le_self N n)) k)
            (pow_nonneg (real_harmonic_nonneg _) _) (by positivity))
      _ = (N : ℝ) * (harmonic N : ℝ) ^ (k + 1) := by
        simp_rw [div_eq_mul_inv, mul_assoc]
        rw [← mul_sum, ← sum_mul, ← real_harmonic_eq_sum, pow_succ]
        ring

/-- Sharp elementary harmonic form of the divisor mean-square bound. -/
theorem sum_card_divisors_sq_le_harmonic (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (n.divisors.card : ℝ) ^ 2) ≤
      (N : ℝ) * (harmonic N : ℝ) ^ 3 := by
  calc
    (∑ n ∈ Ioc 0 N, (n.divisors.card : ℝ) ^ 2)
      ≤ (∑ n ∈ Ioc 0 N, (ζ ^ 4) n : ℕ) := by
        rw [Nat.cast_sum]
        apply sum_le_sum
        intro n hn
        have h : ((n.divisors.card ^ 2 : ℕ) : ℝ) ≤ (((ζ ^ 4) n : ℕ) : ℝ) :=
          Nat.cast_le.mpr (card_divisors_sq_le_zeta_four n)
        simpa only [Nat.cast_pow] using h
    _ ≤ (N : ℝ) * (harmonic N : ℝ) ^ 3 := by
      have h := sum_zeta_pow_le_harmonic 3 N
      simp only [show (3 : ℕ) + 1 = 4 from rfl] at h
      exact h

/-- The classical elementary `N (1 + log N)^3` divisor mean square, including `N = 0`. -/
theorem sum_card_divisors_sq_le_log (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (n.divisors.card : ℝ) ^ 2) ≤
      (N : ℝ) * (1 + Real.log N) ^ 3 := by
  exact (sum_card_divisors_sq_le_harmonic N).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (real_harmonic_nonneg N) (harmonic_le_one_add_log N) 3)
      (Nat.cast_nonneg N))

/-- Coefficient energy for any divisor-bounded sequence in a seminormed group. -/
theorem sum_norm_sq_le_log {E : Type*} [SeminormedAddCommGroup E]
    (b : ℕ → E) (N : ℕ)
    (hb : ∀ n ∈ Ioc 0 N, ‖b n‖ ≤ (n.divisors.card : ℝ)) :
    (∑ n ∈ Ioc 0 N, ‖b n‖ ^ 2) ≤ (N : ℝ) * (1 + Real.log N) ^ 3 := by
  refine (sum_le_sum fun n hn =>
    pow_le_pow_left₀ (norm_nonneg _) (hb n hn) 2).trans (sum_card_divisors_sq_le_log N)

/-- A finite subinterval/subset version, allowing a uniform coefficient multiplier. -/
theorem sum_norm_sq_le_log_of_subset {E : Type*} [SeminormedAddCommGroup E]
    (b : ℕ → E) (T : Finset ℕ) (N : ℕ) (B : ℝ)
    (hT : T ⊆ Ioc 0 N)
    (hb : ∀ n ∈ T, ‖b n‖ ≤ B * (n.divisors.card : ℝ)) :
    (∑ n ∈ T, ‖b n‖ ^ 2) ≤ B ^ 2 * ((N : ℝ) * (1 + Real.log N) ^ 3) := by
  calc
    (∑ n ∈ T, ‖b n‖ ^ 2)
      ≤ ∑ n ∈ T, (B * (n.divisors.card : ℝ)) ^ 2 :=
        sum_le_sum fun n hn => pow_le_pow_left₀ (norm_nonneg _) (hb n hn) 2
    _ = B ^ 2 * ∑ n ∈ T, (n.divisors.card : ℝ) ^ 2 := by
      simp_rw [mul_pow]
      rw [mul_sum]
    _ ≤ B ^ 2 * ∑ n ∈ Ioc 0 N, (n.divisors.card : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => sq_nonneg _)) (sq_nonneg B)
    _ ≤ B ^ 2 * ((N : ℝ) * (1 + Real.log N) ^ 3) :=
      mul_le_mul_of_nonneg_left (sum_card_divisors_sq_le_log N) (sq_nonneg B)

end Problem337.DivisorSquareMean

end

end OAI
