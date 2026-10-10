import OAI.NumberTheory.TwoPointCorrelations.HalaszSmoothSeries
import OAI.NumberTheory.TwoPointCorrelations.HalaszLogConvolution

namespace OAI

/-! The triple-convolution coefficients have a logarithm-squared majorant.
This bounds the short boundary interval in the Perron unsmoothing step. -/

namespace TwoPointCorrelations

open Finset
open scoped LSeries.notation

lemma halasz_mangoldt_convolution_bound (a f : ℕ → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (ha : ∀ n, ‖a n‖ ≤ c * ArithmeticFunction.vonMangoldt n) (hf : OneBounded f) (n : ℕ) :
    ‖(a ⍟ f) n‖ ≤ c * Real.log (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [LSeries.convolution_def]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, c * ArithmeticFunction.vonMangoldt p.1 := by
      apply sum_le_sum
      intro p hp
      have hp0 := (Nat.ne_zero_of_mem_divisorsAntidiagonal hp).2
      rw [norm_mul]
      exact (mul_le_mul (ha p.1) (hf p.2 (Nat.pos_of_ne_zero hp0)) (norm_nonneg _)
        (mul_nonneg hc ArithmeticFunction.vonMangoldt_nonneg)).trans_eq (mul_one _)
    _ = c * Real.log (n : ℝ) := by
      rw [Nat.sum_divisorsAntidiagonal (fun a _ => c * ArithmeticFunction.vonMangoldt a),
        ← mul_sum, ArithmeticFunction.vonMangoldt_sum]

lemma halasz_triple_coefficient_bound (a b f : ℕ → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (ha : ∀ n, ‖a n‖ ≤ c * ArithmeticFunction.vonMangoldt n)
    (hb : ∀ n, ‖b n‖ ≤ ArithmeticFunction.vonMangoldt n) (hf : OneBounded f) (n : ℕ) :
    ‖(a ⍟ (b ⍟ f)) n‖ ≤ c * (Real.log (n : ℝ)) ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hnpos)
  have hinner (m : ℕ) : ‖(b ⍟ f) m‖ ≤ Real.log (m : ℝ) := by
    simpa only [one_mul] using halasz_mangoldt_convolution_bound b f (c := 1)
      (by norm_num) (fun n => by simpa using hb n) hf m
  rw [LSeries.convolution_def]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal,
        c * ArithmeticFunction.vonMangoldt p.1 * Real.log (n : ℝ) := by
      apply sum_le_sum
      intro p hp
      have hpmul := (Nat.mem_divisorsAntidiagonal.mp hp).1
      have hp0 := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
      have hp2pos := Nat.pos_of_ne_zero hp0.2
      have hp2le : p.2 ≤ n := by
        rw [← hpmul]
        exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hp0.1)
      have hlog : Real.log (p.2 : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by exact_mod_cast hp2pos) (by exact_mod_cast hp2le)
      rw [norm_mul]
      exact (mul_le_mul (ha p.1) (hinner p.2) (norm_nonneg _)
        (mul_nonneg hc ArithmeticFunction.vonMangoldt_nonneg)).trans
        (mul_le_mul_of_nonneg_left hlog (mul_nonneg hc ArithmeticFunction.vonMangoldt_nonneg))
    _ = c * Real.log (n : ℝ) ^ 2 := by
      rw [Nat.sum_divisorsAntidiagonal
        (fun a _ => c * ArithmeticFunction.vonMangoldt a * Real.log (n : ℝ)),
        ← sum_mul, ← mul_sum, ArithmeticFunction.vonMangoldt_sum]
      ring

end TwoPointCorrelations

end OAI
