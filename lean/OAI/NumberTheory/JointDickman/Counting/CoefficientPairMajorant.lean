import OAI.NumberTheory.JointDickman.Arithmetic.CoefficientSieveMajorant
import OAI.NumberTheory.JointDickman.Arithmetic.GoodPrimeDensity
import OAI.NumberTheory.JointDickman.Amplification.TwoFormLocalBound

namespace OAI

/-! # The actual two-coefficient weight and its good-prime majorant -/

namespace JointDickman

open Finset

theorem coefficient_pair_le_good_primes (B Z b j n : ℕ) :
    coefficientWeight B n * coefficientWeight B (b + j * n) ≤ coefficientScale B ^ 2 *
      ∏ p ∈ goodSievePrimes Z j b, residueWeight (roughSieveTheta (auxiliaryCutoff B) p) 0 (n : ZMod p) *
        residueWeight (roughSieveTheta (auxiliaryCutoff B) p) 0 ((b : ZMod p) + j * n) := by
  classical
  let f := fun p => residueWeight (roughSieveTheta (auxiliaryCutoff B) p) 0 (n : ZMod p) *
    residueWeight (roughSieveTheta (auxiliaryCutoff B) p) 0 ((b : ZMod p) + j * n)
  have hf0 (p : ℕ) : 0 ≤ f p := mul_nonneg
    (residueWeight_nonneg _ _ (roughSieveTheta_bounds (auxiliaryCutoff B) p).1)
    (residueWeight_nonneg _ _ (roughSieveTheta_bounds (auxiliaryCutoff B) p).1)
  have hf1 (p : ℕ) : f p ≤ 1 := by
    have h := mul_le_mul (residueWeight_le_one (0 : ZMod p) n (roughSieveTheta_bounds (auxiliaryCutoff B) p).2)
      (residueWeight_le_one (0 : ZMod p) ((b : ZMod p) + j * n) (roughSieveTheta_bounds (auxiliaryCutoff B) p).2)
      (residueWeight_nonneg _ _ (roughSieveTheta_bounds (auxiliaryCutoff B) p).1) zero_le_one
    simpa only [mul_one] using h
  have hprod : (∏ p ∈ sievePrimes Z, f p) ≤ ∏ p ∈ goodSievePrimes Z j b, f p :=
    prod_le_prod_of_subset_of_le_one₀ (filter_subset _ _) (fun p _ => hf0 p) (fun p _ _ => hf1 p)
  calc
    _ ≤ (coefficientScale B * sievedCoefficientWeight (auxiliaryCutoff B) Z n) *
        (coefficientScale B * sievedCoefficientWeight (auxiliaryCutoff B) Z (b + j * n)) :=
      mul_le_mul (coefficientWeight_le_sieved B Z n) (coefficientWeight_le_sieved B Z (b + j * n))
        (coefficientWeight_nonneg _ _) (mul_nonneg (coefficientScale_nonneg _) (sievedCoefficientWeight_nonneg _ _ _))
    _ = coefficientScale B ^ 2 * ∏ p ∈ sievePrimes Z, f p := by
      simp only [sievedCoefficientWeight, f, prod_mul_distrib, Nat.cast_add, Nat.cast_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (sq_nonneg _)

end JointDickman

end OAI
