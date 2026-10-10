import OAI.NumberTheory.TwoPointCorrelations.HalaszPrimePowers
import OAI.NumberTheory.TwoPointCorrelations.HalaszLogMean

namespace OAI

/-! Prime-only convolution and its explicit O(N) error. This is the first
step of the Granville--Harper--Soundararajan double-convolution argument. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszPrimeConvolution (f : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ p ∈ (Icc 1 N).filter Nat.Prime,
    (Real.log (p : ℝ) : ℂ) * f p * (∑ m ∈ Icc 1 (N / p), f m)

lemma halasz_log_sum_rows (f : ℕ → ℂ)
    (hf : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n) (N : ℕ) :
    (∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)) =
      ∑ d ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt d : ℂ) * f d *
        (∑ m ∈ Icc 1 (N / d), f m) := by
  rw [halasz_logarithmic_sum f hf N, halasz_hyperbola_rows
    (fun a b => (ArithmeticFunction.vonMangoldt a : ℂ) * f a * f b) N]
  apply sum_congr rfl
  intro d _
  rw [mul_sum]

lemma halasz_prime_convolution_difference (f : ℕ → ℂ)
    (hf : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n) (N : ℕ) :
    (∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)) - halaszPrimeConvolution f N =
      ∑ d ∈ Icc 1 N, (halaszPrimePowerWeight d : ℂ) * f d *
        (∑ m ∈ Icc 1 (N / d), f m) := by
  rw [halasz_log_sum_rows f hf N, halaszPrimeConvolution, sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  by_cases hd : d.Prime
  · simp [hd, halaszPrimePowerWeight, ArithmeticFunction.vonMangoldt_apply_prime hd]
  · simp [hd, halaszPrimePowerWeight]

/-- The exact logarithmic sum differs from its prime-only convolution by
at most a constant times N, uniformly in the bounded multiplicative function. -/
theorem halasz_log_sum_prime_error (f : ℕ → ℂ) (hbound : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n) (N : ℕ) :
    ‖(∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)) - halaszPrimeConvolution f N‖ ≤
      (N : ℝ) * halaszPrimePowerConstant := by
  rw [halasz_prime_convolution_difference f hmul N]
  exact halasz_prime_power_error f hbound N

/-- First Halasz reduction, with a uniform and completely proved error. -/
theorem halasz_prime_convolution_mean_bound (f : ℕ → ℂ) (hbound : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      ‖halaszPrimeConvolution f N‖ + (halaszPrimePowerConstant + 1) * (N : ℝ) := by
  have he := halasz_log_sum_prime_error f hbound hmul N
  have ht := norm_add_le (halaszPrimeConvolution f N)
    ((∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)) - halaszPrimeConvolution f N)
  rw [add_sub_cancel] at ht
  have hh := halasz_logarithmic_mean_bound f hbound N hN
  linarith

end TwoPointCorrelations

end OAI
