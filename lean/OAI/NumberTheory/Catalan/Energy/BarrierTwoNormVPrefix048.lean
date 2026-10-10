import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import OAI.NumberTheory.Catalan.Energy.BarrierTailPairRational

namespace OAI


noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_1 :
    barrierV2 1 ^ 2 / 1 < (970390452 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 1 = (-23910158 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 1 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((-23910158 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 1 +
      (4451662 / 100000000) * (-96 / 100) ^ 1 +
      (2545398 / 100000000) * (88 / 100) ^ 1 +
      (-4932634 / 100000000) * (95 / 100) ^ 1 +
      (11618157 / 100000000) * (984 / 1000) ^ 1 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 1 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 1 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 1 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 1 : ℚ) ^ 2 / 1) <
      970390452 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 1 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_2 :
    barrierV2 2 ^ 2 / 2 < (160633007 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 2 = (21152432 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((21152432 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 2 +
      (4451662 / 100000000) * (-96 / 100) ^ 2 +
      (2545398 / 100000000) * (88 / 100) ^ 2 +
      (-4932634 / 100000000) * (95 / 100) ^ 2 +
      (11618157 / 100000000) * (984 / 1000) ^ 2 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 2 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 2 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 2 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 2 : ℚ) ^ 2 / 2) <
      160633007 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 2 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_3 :
    barrierV2 3 ^ 2 / 3 < (66118369 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 3 = (-2885110 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 3 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((-2885110 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 3 +
      (4451662 / 100000000) * (-96 / 100) ^ 3 +
      (2545398 / 100000000) * (88 / 100) ^ 3 +
      (-4932634 / 100000000) * (95 / 100) ^ 3 +
      (11618157 / 100000000) * (984 / 1000) ^ 3 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 3 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 3 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 3 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 3 : ℚ) ^ 2 / 3) <
      66118369 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 3 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_4 :
    barrierV2 4 ^ 2 / 4 < (1321985 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 4 = (-11558199 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 4 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((-11558199 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 4 +
      (4451662 / 100000000) * (-96 / 100) ^ 4 +
      (2545398 / 100000000) * (88 / 100) ^ 4 +
      (-4932634 / 100000000) * (95 / 100) ^ 4 +
      (11618157 / 100000000) * (984 / 1000) ^ 4 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 4 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 4 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 4 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 4 : ℚ) ^ 2 / 4) <
      1321985 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 4 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_5 :
    barrierV2 5 ^ 2 / 5 < (22281708 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 5 = (6485289 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 5 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((6485289 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 5 +
      (4451662 / 100000000) * (-96 / 100) ^ 5 +
      (2545398 / 100000000) * (88 / 100) ^ 5 +
      (-4932634 / 100000000) * (95 / 100) ^ 5 +
      (11618157 / 100000000) * (984 / 1000) ^ 5 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 5 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 5 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 5 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 5 : ℚ) ^ 2 / 5) <
      22281708 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 5 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_6 :
    barrierV2 6 ^ 2 / 6 < (15772063 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 6 = (1456821 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 6 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((1456821 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 6 +
      (4451662 / 100000000) * (-96 / 100) ^ 6 +
      (2545398 / 100000000) * (88 / 100) ^ 6 +
      (-4932634 / 100000000) * (95 / 100) ^ 6 +
      (11618157 / 100000000) * (984 / 1000) ^ 6 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 6 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 6 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 6 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 6 : ℚ) ^ 2 / 6) <
      15772063 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 6 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_7 :
    barrierV2 7 ^ 2 / 7 < (14164646 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 7 = (-1912176 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 7 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((-1912176 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 7 +
      (4451662 / 100000000) * (-96 / 100) ^ 7 +
      (2545398 / 100000000) * (88 / 100) ^ 7 +
      (-4932634 / 100000000) * (95 / 100) ^ 7 +
      (11618157 / 100000000) * (984 / 1000) ^ 7 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 7 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 7 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 7 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 7 : ℚ) ^ 2 / 7) <
      14164646 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 7 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_8 :
    barrierV2 8 ^ 2 / 8 < (18955 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 8 = (-2263524 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 8 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((-2263524 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 8 +
      (4451662 / 100000000) * (-96 / 100) ^ 8 +
      (2545398 / 100000000) * (88 / 100) ^ 8 +
      (-4932634 / 100000000) * (95 / 100) ^ 8 +
      (11618157 / 100000000) * (984 / 1000) ^ 8 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 8 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 8 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 8 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 8 : ℚ) ^ 2 / 8) <
      18955 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 8 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_8 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (0 + k + 1) ^ 2 / ((0 + k + 1 : ℕ) : ℝ)) ≤
      (1250701185 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_1.le) barrierV2_norm_term_2.le) barrierV2_norm_term_3.le) barrierV2_norm_term_4.le) barrierV2_norm_term_5.le) barrierV2_norm_term_6.le) barrierV2_norm_term_7.le) barrierV2_norm_term_8.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_8 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1250701185 / 1000000000 : ℝ) := by
  simpa only [Nat.zero_add] using barrierV2_norm_block_8

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_9 :
    barrierV2 9 ^ 2 / 9 < (5065162 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 9 = (2742210 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 9 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((2742210 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 9 +
      (4451662 / 100000000) * (-96 / 100) ^ 9 +
      (2545398 / 100000000) * (88 / 100) ^ 9 +
      (-4932634 / 100000000) * (95 / 100) ^ 9 +
      (11618157 / 100000000) * (984 / 1000) ^ 9 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 9 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 9 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 9 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 9 : ℚ) ^ 2 / 9) <
      5065162 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 9 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_10 :
    barrierV2 10 ^ 2 / 10 < (4930284 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 10 = (-1162454 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 10 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((-1162454 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 10 +
      (4451662 / 100000000) * (-96 / 100) ^ 10 +
      (2545398 / 100000000) * (88 / 100) ^ 10 +
      (-4932634 / 100000000) * (95 / 100) ^ 10 +
      (11618157 / 100000000) * (984 / 1000) ^ 10 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 10 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 10 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 10 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 10 : ℚ) ^ 2 / 10) <
      4930284 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 10 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_11 :
    barrierV2 11 ^ 2 / 11 < (6326889 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 11 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 11 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 11 +
      (4451662 / 100000000) * (-96 / 100) ^ 11 +
      (2545398 / 100000000) * (88 / 100) ^ 11 +
      (-4932634 / 100000000) * (95 / 100) ^ 11 +
      (11618157 / 100000000) * (984 / 1000) ^ 11 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 11 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 11 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 11 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 11 : ℚ) ^ 2 / 11) <
      6326889 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 11 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_12 :
    barrierV2 12 ^ 2 / 12 < (21348 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 12 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 12 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 12 +
      (4451662 / 100000000) * (-96 / 100) ^ 12 +
      (2545398 / 100000000) * (88 / 100) ^ 12 +
      (-4932634 / 100000000) * (95 / 100) ^ 12 +
      (11618157 / 100000000) * (984 / 1000) ^ 12 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 12 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 12 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 12 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 12 : ℚ) ^ 2 / 12) <
      21348 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 12 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_13 :
    barrierV2 13 ^ 2 / 13 < (2053383 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 13 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 13 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 13 +
      (4451662 / 100000000) * (-96 / 100) ^ 13 +
      (2545398 / 100000000) * (88 / 100) ^ 13 +
      (-4932634 / 100000000) * (95 / 100) ^ 13 +
      (11618157 / 100000000) * (984 / 1000) ^ 13 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 13 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 13 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 13 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 13 : ℚ) ^ 2 / 13) <
      2053383 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 13 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_14 :
    barrierV2 14 ^ 2 / 14 < (2490942 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 14 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 14 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 14 +
      (4451662 / 100000000) * (-96 / 100) ^ 14 +
      (2545398 / 100000000) * (88 / 100) ^ 14 +
      (-4932634 / 100000000) * (95 / 100) ^ 14 +
      (11618157 / 100000000) * (984 / 1000) ^ 14 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 14 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 14 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 14 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 14 : ℚ) ^ 2 / 14) <
      2490942 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 14 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero,
    zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_15 :
    barrierV2 15 ^ 2 / 15 < (3369446 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 15 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 15 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 15 +
      (4451662 / 100000000) * (-96 / 100) ^ 15 +
      (2545398 / 100000000) * (88 / 100) ^ 15 +
      (-4932634 / 100000000) * (95 / 100) ^ 15 +
      (11618157 / 100000000) * (984 / 1000) ^ 15 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 15 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 15 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 15 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 15 : ℚ) ^ 2 / 15) <
      3369446 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 15 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_16 :
    barrierV2 16 ^ 2 / 16 < (54967 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 16 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 16 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 16 +
      (4451662 / 100000000) * (-96 / 100) ^ 16 +
      (2545398 / 100000000) * (88 / 100) ^ 16 +
      (-4932634 / 100000000) * (95 / 100) ^ 16 +
      (11618157 / 100000000) * (984 / 1000) ^ 16 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 16 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 16 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 16 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 16 : ℚ) ^ 2 / 16) <
      54967 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 16 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_16 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (8 + k + 1) ^ 2 / ((8 + k + 1 : ℕ) : ℝ)) ≤
      (24312421 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_9.le) barrierV2_norm_term_10.le) barrierV2_norm_term_11.le) barrierV2_norm_term_12.le) barrierV2_norm_term_13.le) barrierV2_norm_term_14.le) barrierV2_norm_term_15.le) barrierV2_norm_term_16.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_16 :
    (∑ k ∈ Finset.range 16,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1275013606 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (8 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_8 barrierV2_norm_block_16
  have hc : (1250701185 / 1000000000 : ℝ) + 24312421 / 1000000000 =
      1275013606 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_17 :
    barrierV2 17 ^ 2 / 17 < (870796 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 17 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 17 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 17 +
      (4451662 / 100000000) * (-96 / 100) ^ 17 +
      (2545398 / 100000000) * (88 / 100) ^ 17 +
      (-4932634 / 100000000) * (95 / 100) ^ 17 +
      (11618157 / 100000000) * (984 / 1000) ^ 17 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 17 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 17 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 17 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 17 : ℚ) ^ 2 / 17) <
      870796 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 17 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_18 :
    barrierV2 18 ^ 2 / 18 < (1279000 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 18 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 18 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 18 +
      (4451662 / 100000000) * (-96 / 100) ^ 18 +
      (2545398 / 100000000) * (88 / 100) ^ 18 +
      (-4932634 / 100000000) * (95 / 100) ^ 18 +
      (11618157 / 100000000) * (984 / 1000) ^ 18 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 18 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 18 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 18 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 18 : ℚ) ^ 2 / 18) <
      1279000 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 18 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero,
    zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_19 :
    barrierV2 19 ^ 2 / 19 < (2122938 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 19 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 19 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 19 +
      (4451662 / 100000000) * (-96 / 100) ^ 19 +
      (2545398 / 100000000) * (88 / 100) ^ 19 +
      (-4932634 / 100000000) * (95 / 100) ^ 19 +
      (11618157 / 100000000) * (984 / 1000) ^ 19 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 19 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 19 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 19 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 19 : ℚ) ^ 2 / 19) <
      2122938 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 19 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_20 :
    barrierV2 20 ^ 2 / 20 < (87741 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 20 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 20 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 20 +
      (4451662 / 100000000) * (-96 / 100) ^ 20 +
      (2545398 / 100000000) * (88 / 100) ^ 20 +
      (-4932634 / 100000000) * (95 / 100) ^ 20 +
      (11618157 / 100000000) * (984 / 1000) ^ 20 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 20 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 20 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 20 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 20 : ℚ) ^ 2 / 20) <
      87741 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 20 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_21 :
    barrierV2 21 ^ 2 / 21 < (449313 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 21 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 21 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 21 +
      (4451662 / 100000000) * (-96 / 100) ^ 21 +
      (2545398 / 100000000) * (88 / 100) ^ 21 +
      (-4932634 / 100000000) * (95 / 100) ^ 21 +
      (11618157 / 100000000) * (984 / 1000) ^ 21 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 21 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 21 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 21 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 21 : ℚ) ^ 2 / 21) <
      449313 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 21 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_22 :
    barrierV2 22 ^ 2 / 22 < (720581 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 22 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 22 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 22 +
      (4451662 / 100000000) * (-96 / 100) ^ 22 +
      (2545398 / 100000000) * (88 / 100) ^ 22 +
      (-4932634 / 100000000) * (95 / 100) ^ 22 +
      (11618157 / 100000000) * (984 / 1000) ^ 22 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 22 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 22 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 22 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 22 : ℚ) ^ 2 / 22) <
      720581 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 22 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero,
    zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_23 :
    barrierV2 23 ^ 2 / 23 < (1481876 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 23 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 23 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 23 +
      (4451662 / 100000000) * (-96 / 100) ^ 23 +
      (2545398 / 100000000) * (88 / 100) ^ 23 +
      (-4932634 / 100000000) * (95 / 100) ^ 23 +
      (11618157 / 100000000) * (984 / 1000) ^ 23 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 23 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 23 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 23 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 23 : ℚ) ^ 2 / 23) <
      1481876 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 23 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_24 :
    barrierV2 24 ^ 2 / 24 < (106633 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 24 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 24 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 24 +
      (4451662 / 100000000) * (-96 / 100) ^ 24 +
      (2545398 / 100000000) * (88 / 100) ^ 24 +
      (-4932634 / 100000000) * (95 / 100) ^ 24 +
      (11618157 / 100000000) * (984 / 1000) ^ 24 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 24 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 24 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 24 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 24 : ℚ) ^ 2 / 24) <
      106633 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 24 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_24 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (16 + k + 1) ^ 2 / ((16 + k + 1 : ℕ) : ℝ)) ≤
      (7118878 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_17.le) barrierV2_norm_term_18.le) barrierV2_norm_term_19.le) barrierV2_norm_term_20.le) barrierV2_norm_term_21.le) barrierV2_norm_term_22.le) barrierV2_norm_term_23.le) barrierV2_norm_term_24.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_24 :
    (∑ k ∈ Finset.range 24,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1282132484 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (16 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_16 barrierV2_norm_block_24
  have hc : (1275013606 / 1000000000 : ℝ) + 7118878 / 1000000000 =
      1282132484 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_25 :
    barrierV2 25 ^ 2 / 25 < (265648 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 25 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 25 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 25 +
      (4451662 / 100000000) * (-96 / 100) ^ 25 +
      (2545398 / 100000000) * (88 / 100) ^ 25 +
      (-4932634 / 100000000) * (95 / 100) ^ 25 +
      (11618157 / 100000000) * (984 / 1000) ^ 25 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 25 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 25 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 25 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 25 : ℚ) ^ 2 / 25) <
      265648 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 25 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_26 :
    barrierV2 26 ^ 2 / 26 < (437835 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 26 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 26 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 26 +
      (4451662 / 100000000) * (-96 / 100) ^ 26 +
      (2545398 / 100000000) * (88 / 100) ^ 26 +
      (-4932634 / 100000000) * (95 / 100) ^ 26 +
      (11618157 / 100000000) * (984 / 1000) ^ 26 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 26 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 26 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 26 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 26 : ℚ) ^ 2 / 26) <
      437835 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 26 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero,
    zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_27 :
    barrierV2 27 ^ 2 / 27 < (1103608 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 27 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 27 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 27 +
      (4451662 / 100000000) * (-96 / 100) ^ 27 +
      (2545398 / 100000000) * (88 / 100) ^ 27 +
      (-4932634 / 100000000) * (95 / 100) ^ 27 +
      (11618157 / 100000000) * (984 / 1000) ^ 27 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 27 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 27 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 27 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 27 : ℚ) ^ 2 / 27) <
      1103608 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 27 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_28 :
    barrierV2 28 ^ 2 / 28 < (111715 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 28 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 28 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 28 +
      (4451662 / 100000000) * (-96 / 100) ^ 28 +
      (2545398 / 100000000) * (88 / 100) ^ 28 +
      (-4932634 / 100000000) * (95 / 100) ^ 28 +
      (11618157 / 100000000) * (984 / 1000) ^ 28 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 28 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 28 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 28 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 28 : ℚ) ^ 2 / 28) <
      111715 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 28 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_29 :
    barrierV2 29 ^ 2 / 29 < (172849 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 29 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 29 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 29 +
      (4451662 / 100000000) * (-96 / 100) ^ 29 +
      (2545398 / 100000000) * (88 / 100) ^ 29 +
      (-4932634 / 100000000) * (95 / 100) ^ 29 +
      (11618157 / 100000000) * (984 / 1000) ^ 29 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 29 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 29 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 29 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 29 : ℚ) ^ 2 / 29) <
      172849 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 29 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_30 :
    barrierV2 30 ^ 2 / 30 < (282884 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 30 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 30 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 30 +
      (4451662 / 100000000) * (-96 / 100) ^ 30 +
      (2545398 / 100000000) * (88 / 100) ^ 30 +
      (-4932634 / 100000000) * (95 / 100) ^ 30 +
      (11618157 / 100000000) * (984 / 1000) ^ 30 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 30 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 30 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 30 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 30 : ℚ) ^ 2 / 30) <
      282884 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 30 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero,
    zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_31 :
    barrierV2 31 ^ 2 / 31 < (857115 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 31 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 31 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 31 +
      (4451662 / 100000000) * (-96 / 100) ^ 31 +
      (2545398 / 100000000) * (88 / 100) ^ 31 +
      (-4932634 / 100000000) * (95 / 100) ^ 31 +
      (11618157 / 100000000) * (984 / 1000) ^ 31 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 31 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 31 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 31 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 31 : ℚ) ^ 2 / 31) <
      857115 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 31 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_32 :
    barrierV2 32 ^ 2 / 32 < (107492 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 32 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 32 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 32 +
      (4451662 / 100000000) * (-96 / 100) ^ 32 +
      (2545398 / 100000000) * (88 / 100) ^ 32 +
      (-4932634 / 100000000) * (95 / 100) ^ 32 +
      (11618157 / 100000000) * (984 / 1000) ^ 32 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 32 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 32 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 32 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 32 : ℚ) ^ 2 / 32) <
      107492 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 32 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_32 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (24 + k + 1) ^ 2 / ((24 + k + 1 : ℕ) : ℝ)) ≤
      (3339146 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_25.le) barrierV2_norm_term_26.le) barrierV2_norm_term_27.le) barrierV2_norm_term_28.le) barrierV2_norm_term_29.le) barrierV2_norm_term_30.le) barrierV2_norm_term_31.le) barrierV2_norm_term_32.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_32 :
    (∑ k ∈ Finset.range 32,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1285471630 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (24 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_24 barrierV2_norm_block_32
  have hc : (1282132484 / 1000000000 : ℝ) + 3339146 / 1000000000 =
      1285471630 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_33 :
    barrierV2 33 ^ 2 / 33 < (120428 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 33 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 33 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 33 +
      (4451662 / 100000000) * (-96 / 100) ^ 33 +
      (2545398 / 100000000) * (88 / 100) ^ 33 +
      (-4932634 / 100000000) * (95 / 100) ^ 33 +
      (11618157 / 100000000) * (984 / 1000) ^ 33 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 33 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 33 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 33 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 33 : ℚ) ^ 2 / 33) <
      120428 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 33 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_34 :
    barrierV2 34 ^ 2 / 34 < (192033 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 34 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 34 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 34 +
      (4451662 / 100000000) * (-96 / 100) ^ 34 +
      (2545398 / 100000000) * (88 / 100) ^ 34 +
      (-4932634 / 100000000) * (95 / 100) ^ 34 +
      (11618157 / 100000000) * (984 / 1000) ^ 34 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 34 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 34 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 34 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 34 : ℚ) ^ 2 / 34) <
      192033 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 34 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero,
    zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_35 :
    barrierV2 35 ^ 2 / 35 < (684331 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 35 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 35 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 35 +
      (4451662 / 100000000) * (-96 / 100) ^ 35 +
      (2545398 / 100000000) * (88 / 100) ^ 35 +
      (-4932634 / 100000000) * (95 / 100) ^ 35 +
      (11618157 / 100000000) * (984 / 1000) ^ 35 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 35 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 35 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 35 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 35 : ℚ) ^ 2 / 35) <
      684331 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 35 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_36 :
    barrierV2 36 ^ 2 / 36 < (98292 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 36 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 36 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 36 +
      (4451662 / 100000000) * (-96 / 100) ^ 36 +
      (2545398 / 100000000) * (88 / 100) ^ 36 +
      (-4932634 / 100000000) * (95 / 100) ^ 36 +
      (11618157 / 100000000) * (984 / 1000) ^ 36 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 36 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 36 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 36 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 36 : ℚ) ^ 2 / 36) <
      98292 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 36 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_37 :
    barrierV2 37 ^ 2 / 37 < (88154 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 37 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 37 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 37 +
      (4451662 / 100000000) * (-96 / 100) ^ 37 +
      (2545398 / 100000000) * (88 / 100) ^ 37 +
      (-4932634 / 100000000) * (95 / 100) ^ 37 +
      (11618157 / 100000000) * (984 / 1000) ^ 37 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 37 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 37 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 37 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 37 : ℚ) ^ 2 / 37) <
      88154 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 37 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_38 :
    barrierV2 38 ^ 2 / 38 < (135606 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 38 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 38 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 38 +
      (4451662 / 100000000) * (-96 / 100) ^ 38 +
      (2545398 / 100000000) * (88 / 100) ^ 38 +
      (-4932634 / 100000000) * (95 / 100) ^ 38 +
      (11618157 / 100000000) * (984 / 1000) ^ 38 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 38 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 38 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 38 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 38 : ℚ) ^ 2 / 38) <
      135606 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 38 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero,
    zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_39 :
    barrierV2 39 ^ 2 / 39 < (556543 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 39 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 39 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 39 +
      (4451662 / 100000000) * (-96 / 100) ^ 39 +
      (2545398 / 100000000) * (88 / 100) ^ 39 +
      (-4932634 / 100000000) * (95 / 100) ^ 39 +
      (11618157 / 100000000) * (984 / 1000) ^ 39 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 39 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 39 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 39 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 39 : ℚ) ^ 2 / 39) <
      556543 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 39 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_40 :
    barrierV2 40 ^ 2 / 40 < (87104 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 40 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 40 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 40 +
      (4451662 / 100000000) * (-96 / 100) ^ 40 +
      (2545398 / 100000000) * (88 / 100) ^ 40 +
      (-4932634 / 100000000) * (95 / 100) ^ 40 +
      (11618157 / 100000000) * (984 / 1000) ^ 40 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 40 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 40 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 40 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 40 : ℚ) ^ 2 / 40) <
      87104 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 40 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_40 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (32 + k + 1) ^ 2 / ((32 + k + 1 : ℕ) : ℝ)) ≤
      (1962491 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_33.le) barrierV2_norm_term_34.le) barrierV2_norm_term_35.le) barrierV2_norm_term_36.le) barrierV2_norm_term_37.le) barrierV2_norm_term_38.le) barrierV2_norm_term_39.le) barrierV2_norm_term_40.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_40 :
    (∑ k ∈ Finset.range 40,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1287434121 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (32 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_32 barrierV2_norm_block_40
  have hc : (1285471630 / 1000000000 : ℝ) + 1962491 / 1000000000 =
      1287434121 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_41 :
    barrierV2 41 ^ 2 / 41 < (66892 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 41 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 41 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 41 +
      (4451662 / 100000000) * (-96 / 100) ^ 41 +
      (2545398 / 100000000) * (88 / 100) ^ 41 +
      (-4932634 / 100000000) * (95 / 100) ^ 41 +
      (11618157 / 100000000) * (984 / 1000) ^ 41 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 41 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 41 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 41 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 41 : ℚ) ^ 2 / 41) <
      66892 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 41 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_42 :
    barrierV2 42 ^ 2 / 42 < (98809 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 42 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 42 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 42 +
      (4451662 / 100000000) * (-96 / 100) ^ 42 +
      (2545398 / 100000000) * (88 / 100) ^ 42 +
      (-4932634 / 100000000) * (95 / 100) ^ 42 +
      (11618157 / 100000000) * (984 / 1000) ^ 42 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 42 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 42 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 42 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 42 : ℚ) ^ 2 / 42) <
      98809 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 42 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero,
    zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_43 :
    barrierV2 43 ^ 2 / 43 < (458279 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 43 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 43 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 43 +
      (4451662 / 100000000) * (-96 / 100) ^ 43 +
      (2545398 / 100000000) * (88 / 100) ^ 43 +
      (-4932634 / 100000000) * (95 / 100) ^ 43 +
      (11618157 / 100000000) * (984 / 1000) ^ 43 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 43 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 43 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 43 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 43 : ℚ) ^ 2 / 43) <
      458279 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 43 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_44 :
    barrierV2 44 ^ 2 / 44 < (75686 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 44 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 44 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 44 +
      (4451662 / 100000000) * (-96 / 100) ^ 44 +
      (2545398 / 100000000) * (88 / 100) ^ 44 +
      (-4932634 / 100000000) * (95 / 100) ^ 44 +
      (11618157 / 100000000) * (984 / 1000) ^ 44 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 44 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 44 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 44 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 44 : ℚ) ^ 2 / 44) <
      75686 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 44 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_45 :
    barrierV2 45 ^ 2 / 45 < (52113 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 45 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 45 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 45 +
      (4451662 / 100000000) * (-96 / 100) ^ 45 +
      (2545398 / 100000000) * (88 / 100) ^ 45 +
      (-4932634 / 100000000) * (95 / 100) ^ 45 +
      (11618157 / 100000000) * (984 / 1000) ^ 45 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 45 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 45 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 45 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 45 : ℚ) ^ 2 / 45) <
      52113 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 45 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_46 :
    barrierV2 46 ^ 2 / 46 < (73815 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 46 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 46 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 46 +
      (4451662 / 100000000) * (-96 / 100) ^ 46 +
      (2545398 / 100000000) * (88 / 100) ^ 46 +
      (-4932634 / 100000000) * (95 / 100) ^ 46 +
      (11618157 / 100000000) * (984 / 1000) ^ 46 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 46 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 46 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 46 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 46 : ℚ) ^ 2 / 46) <
      73815 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 46 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero,
    zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_47 :
    barrierV2 47 ^ 2 / 47 < (380579 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 47 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 47 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 47 +
      (4451662 / 100000000) * (-96 / 100) ^ 47 +
      (2545398 / 100000000) * (88 / 100) ^ 47 +
      (-4932634 / 100000000) * (95 / 100) ^ 47 +
      (11618157 / 100000000) * (984 / 1000) ^ 47 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 47 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 47 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 47 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 47 : ℚ) ^ 2 / 47) <
      380579 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 47 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_48 :
    barrierV2 48 ^ 2 / 48 < (64952 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 48 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 48 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 48 +
      (4451662 / 100000000) * (-96 / 100) ^ 48 +
      (2545398 / 100000000) * (88 / 100) ^ 48 +
      (-4932634 / 100000000) * (95 / 100) ^ 48 +
      (11618157 / 100000000) * (984 / 1000) ^ 48 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 48 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 48 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 48 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 48 : ℚ) ^ 2 / 48) <
      64952 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 48 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_48 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (40 + k + 1) ^ 2 / ((40 + k + 1 : ℕ) : ℝ)) ≤
      (1271125 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_41.le) barrierV2_norm_term_42.le) barrierV2_norm_term_43.le) barrierV2_norm_term_44.le) barrierV2_norm_term_45.le) barrierV2_norm_term_46.le) barrierV2_norm_term_47.le) barrierV2_norm_term_48.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_48 :
    (∑ k ∈ Finset.range 48,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1288705246 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (40 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_40 barrierV2_norm_block_48
  have hc : (1287434121 / 1000000000 : ℝ) + 1271125 / 1000000000 =
      1288705246 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end

end OAI
