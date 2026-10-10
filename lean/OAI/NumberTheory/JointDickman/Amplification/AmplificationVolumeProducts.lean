import OAI.NumberTheory.JointDickman.Probability.ResidueProductMean
import OAI.NumberTheory.JointDickman.Amplification.ArithmeticPeriod
import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryOdds

namespace OAI

/-! # The coefficient harmonic mass cancels the residue-weight mean -/

namespace JointDickman
open Finset

noncomputable def baseArithmeticResidueWeight (B n : ℕ) : ℝ :=
  residueBaseWeight B (coefficientPrimeSet B n)

noncomputable def baseArithmeticResidueMean (B : ℕ) : ℝ :=
  auxiliaryRatio B ^ (1/2 : ℝ) * primeNormalizer (auxiliaryPrimes B) (1/2)

theorem baseArithmeticResidueWeight_product (B n : ℕ) :
    baseArithmeticResidueWeight B n = auxiliaryRatio B ^ (1/2 : ℝ) *
      ∏ p ∈ auxiliaryPrimes B, if p ∣ n then (1/2 : ℝ) else 1 := by
  unfold baseArithmeticResidueWeight residueBaseWeight coefficientPrimeSet
  rw [← prod_const, prod_filter]

theorem baseArithmeticResidueWeight_mean (B : ℕ) :
    (∑ a : ZMod (auxiliarySquarePeriod B), baseArithmeticResidueWeight B a.val) /
      (auxiliarySquarePeriod B : ℝ) = baseArithmeticResidueMean B := by
  have hd : (∏ p ∈ auxiliaryPrimes B, p) ∣ auxiliarySquarePeriod B := by
    unfold auxiliarySquarePeriod
    exact dvd_pow_self _ (by norm_num : 2 ≠ 0)
  have h := residue_divisor_product_mean (auxiliaryPrimes B) (auxiliaryPrimes_prime B) hd
    (fun _ => (-1/2 : ℝ))
  simp only [show (1 : ℝ) + -1/2 = 1/2 by norm_num] at h
  simp_rw [baseArithmeticResidueWeight_product]
  rw [← mul_sum, mul_div_assoc, h]
  unfold baseArithmeticResidueMean primeNormalizer
  congr 1
  apply prod_congr rfl
  intro p _
  ring

theorem coefficient_harmonic_product (B : ℕ) :
    (∑ D ∈ (auxiliaryPrimes B).powerset,
      coefficientWeight B (∏ p ∈ D, p) / (∏ p ∈ D, (p : ℝ))) =
      coefficientScale B * ∏ p ∈ auxiliaryPrimes B, (1 + (1/2 : ℝ)/p) := by
  rw [prod_one_add, mul_sum]
  apply sum_congr rfl
  intro D hD
  rw [coefficientWeight_primeProduct (mem_powerset.mp hD)]
  simp only [residueBaseWeight, coefficientScale, prod_div_distrib, prod_const, one_div]
  ring

/-- This exact finite cancellation bounds the Cauchy volume without a
further interval asymptotic: the leftover Euler factors are at most one. -/
theorem coefficient_harmonic_mul_residueMean_le {B : ℕ} (hB : 1 < B) :
    (∑ D ∈ (auxiliaryPrimes B).powerset,
      coefficientWeight B (∏ p ∈ D, p) / (∏ p ∈ D, (p : ℝ))) *
      baseArithmeticResidueMean B ≤ B := by
  rw [coefficient_harmonic_product, baseArithmeticResidueMean]
  have he : (coefficientScale B * ∏ p ∈ auxiliaryPrimes B, (1+(1/2 : ℝ)/p)) *
      (auxiliaryRatio B^(1/2 : ℝ) * primeNormalizer (auxiliaryPrimes B) (1/2)) =
      (B : ℝ) * ∏ p ∈ auxiliaryPrimes B, (1 - ((1/2 : ℝ)/p)^2) := by
    rw [mul_mul_mul_comm, coefficientScale_mul_sqrt_ratio hB]
    unfold primeNormalizer
    rw [← prod_mul_distrib]
    congr 1
    apply prod_congr rfl
    intro p _
    ring
  rw [he]
  apply mul_le_of_le_one_right (Nat.cast_nonneg B)
  apply prod_le_one₀
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hd : (1/2 : ℝ)/p ≤ 1 := (div_le_one hp0).mpr (by linarith)
    have hn : 0 ≤ (1/2 : ℝ)/p := by positivity
    nlinarith
  · intro p _
    exact sub_le_self _ (sq_nonneg _)

end JointDickman

end OAI
