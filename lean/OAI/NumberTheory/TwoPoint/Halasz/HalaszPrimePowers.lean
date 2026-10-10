import OAI.NumberTheory.TwoPoint.Halasz.HalaszHyperbolaRows
import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace OAI

/-! The total reciprocal contribution of higher prime powers is finite.
The modulus-one specialization of the prime-power series bounds
the finite hyperbola error. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszPrimePowerWeight (n : ℕ) : ℝ :=
  if n.Prime then 0 else ArithmeticFunction.vonMangoldt n

lemma halaszPrimePowerWeight_nonneg (n : ℕ) : 0 ≤ halaszPrimePowerWeight n := by
  unfold halaszPrimePowerWeight
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

lemma halaszPrimePowerWeight_summable :
    Summable (fun n : ℕ => halaszPrimePowerWeight n / (n : ℝ)) := by
  have hh := ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div
    (0 : ZMod 1)
  convert hh using 1
  funext n
  simp only [halaszPrimePowerWeight, ArithmeticFunction.vonMangoldt.residueClass]
  have he : (n : ZMod 1) = 0 := Subsingleton.elim _ _
  simp [he]

noncomputable def halaszPrimePowerConstant : ℝ :=
  ∑' n : ℕ, halaszPrimePowerWeight n / (n : ℝ)

lemma halaszPrimePowerConstant_nonneg : 0 ≤ halaszPrimePowerConstant :=
  tsum_nonneg (fun n => div_nonneg (halaszPrimePowerWeight_nonneg n) (Nat.cast_nonneg _))

lemma halasz_bounded_prefix_norm (f : ℕ → ℂ) (hf : OneBounded f) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, f n‖ ≤ (N : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Icc 1 N, (1 : ℝ) :=
      sum_le_sum (fun n hn => hf n (mem_Icc.mp hn).1)
    _ = _ := by simp

/-- Discarding all higher prime powers in the logarithmic hyperbola incurs
at most an absolute constant times its outer cutoff. -/
theorem halasz_prime_power_error (f : ℕ → ℂ) (hf : OneBounded f) (N : ℕ) :
    ‖∑ d ∈ Icc 1 N, (halaszPrimePowerWeight d : ℂ) * f d *
      (∑ m ∈ Icc 1 (N / d), f m)‖ ≤ (N : ℝ) * halaszPrimePowerConstant := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ d ∈ Icc 1 N, (N : ℝ) * (halaszPrimePowerWeight d / (d : ℝ)) := by
      apply sum_le_sum
      intro d hd
      have hdpos := (mem_Icc.mp hd).1
      have hdr : (0 : ℝ) < d := by exact_mod_cast hdpos
      have hw := halaszPrimePowerWeight_nonneg d
      have hdiv : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
        apply (le_div_iff₀ hdr).mpr
        exact_mod_cast Nat.div_mul_le_self N d
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
      calc
        _ ≤ halaszPrimePowerWeight d * 1 * ((N / d : ℕ) : ℝ) := by
          gcongr
          · exact hf d hdpos
          · exact halasz_bounded_prefix_norm f hf (N / d)
        _ ≤ halaszPrimePowerWeight d * ((N : ℝ) / (d : ℝ)) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hdiv hw
        _ = _ := by ring
    _ = (N : ℝ) * ∑ d ∈ Icc 1 N, halaszPrimePowerWeight d / (d : ℝ) :=
      (mul_sum _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact halaszPrimePowerWeight_summable.sum_le_tsum _
        (fun d _ => div_nonneg (halaszPrimePowerWeight_nonneg d) (Nat.cast_nonneg _))

end TwoPointCorrelations

end OAI
