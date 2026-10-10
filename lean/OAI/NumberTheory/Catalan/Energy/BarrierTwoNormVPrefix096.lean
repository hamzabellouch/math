import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import OAI.NumberTheory.Catalan.Energy.BarrierTwoNormVPrefix048

namespace OAI


noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_49 :
    barrierV2 49 ^ 2 / 49 < (41395 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 49 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 49 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 49 +
      (4451662 / 100000000) * (-96 / 100) ^ 49 +
      (2545398 / 100000000) * (88 / 100) ^ 49 +
      (-4932634 / 100000000) * (95 / 100) ^ 49 +
      (11618157 / 100000000) * (984 / 1000) ^ 49 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 49 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 49 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 49 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 49 : ℚ) ^ 2 / 49) <
      41395 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 49 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_50 :
    barrierV2 50 ^ 2 / 50 < (56252 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 50 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 50 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 50 +
      (4451662 / 100000000) * (-96 / 100) ^ 50 +
      (2545398 / 100000000) * (88 / 100) ^ 50 +
      (-4932634 / 100000000) * (95 / 100) ^ 50 +
      (11618157 / 100000000) * (984 / 1000) ^ 50 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 50 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 50 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 50 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 50 : ℚ) ^ 2 / 50) <
      56252 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 50 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_51 :
    barrierV2 51 ^ 2 / 51 < (317915 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 51 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 51 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 51 +
      (4451662 / 100000000) * (-96 / 100) ^ 51 +
      (2545398 / 100000000) * (88 / 100) ^ 51 +
      (-4932634 / 100000000) * (95 / 100) ^ 51 +
      (11618157 / 100000000) * (984 / 1000) ^ 51 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 51 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 51 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 51 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 51 : ℚ) ^ 2 / 51) <
      317915 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 51 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_52 :
    barrierV2 52 ^ 2 / 52 < (55307 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 52 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 52 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 52 +
      (4451662 / 100000000) * (-96 / 100) ^ 52 +
      (2545398 / 100000000) * (88 / 100) ^ 52 +
      (-4932634 / 100000000) * (95 / 100) ^ 52 +
      (11618157 / 100000000) * (984 / 1000) ^ 52 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 52 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 52 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 52 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 52 : ℚ) ^ 2 / 52) <
      55307 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 52 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_53 :
    barrierV2 53 ^ 2 / 53 < (33358 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 53 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 53 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 53 +
      (4451662 / 100000000) * (-96 / 100) ^ 53 +
      (2545398 / 100000000) * (88 / 100) ^ 53 +
      (-4932634 / 100000000) * (95 / 100) ^ 53 +
      (11618157 / 100000000) * (984 / 1000) ^ 53 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 53 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 53 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 53 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 53 : ℚ) ^ 2 / 53) <
      33358 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 53 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_54 :
    barrierV2 54 ^ 2 / 54 < (43560 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 54 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 54 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 54 +
      (4451662 / 100000000) * (-96 / 100) ^ 54 +
      (2545398 / 100000000) * (88 / 100) ^ 54 +
      (-4932634 / 100000000) * (95 / 100) ^ 54 +
      (11618157 / 100000000) * (984 / 1000) ^ 54 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 54 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 54 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 54 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 54 : ℚ) ^ 2 / 54) <
      43560 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 54 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_55 :
    barrierV2 55 ^ 2 / 55 < (266670 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 55 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 55 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 55 +
      (4451662 / 100000000) * (-96 / 100) ^ 55 +
      (2545398 / 100000000) * (88 / 100) ^ 55 +
      (-4932634 / 100000000) * (95 / 100) ^ 55 +
      (11618157 / 100000000) * (984 / 1000) ^ 55 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 55 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 55 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 55 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 55 : ℚ) ^ 2 / 55) <
      266670 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 55 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_56 :
    barrierV2 56 ^ 2 / 56 < (46867 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 56 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 56 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 56 +
      (4451662 / 100000000) * (-96 / 100) ^ 56 +
      (2545398 / 100000000) * (88 / 100) ^ 56 +
      (-4932634 / 100000000) * (95 / 100) ^ 56 +
      (11618157 / 100000000) * (984 / 1000) ^ 56 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 56 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 56 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 56 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 56 : ℚ) ^ 2 / 56) <
      46867 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 56 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_56 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (48 + k + 1) ^ 2 / ((48 + k + 1 : ℕ) : ℝ)) ≤
      (861324 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_49.le) barrierV2_norm_term_50.le) barrierV2_norm_term_51.le) barrierV2_norm_term_52.le) barrierV2_norm_term_53.le) barrierV2_norm_term_54.le) barrierV2_norm_term_55.le) barrierV2_norm_term_56.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_56 :
    (∑ k ∈ Finset.range 56,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1289566570 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (48 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_48 barrierV2_norm_block_56
  have hc : (1288705246 / 1000000000 : ℝ) + 861324 / 1000000000 =
      1289566570 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_57 :
    barrierV2 57 ^ 2 / 57 < (27174 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 57 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 57 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 57 +
      (4451662 / 100000000) * (-96 / 100) ^ 57 +
      (2545398 / 100000000) * (88 / 100) ^ 57 +
      (-4932634 / 100000000) * (95 / 100) ^ 57 +
      (11618157 / 100000000) * (984 / 1000) ^ 57 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 57 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 57 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 57 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 57 : ℚ) ^ 2 / 57) <
      27174 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 57 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_58 :
    barrierV2 58 ^ 2 / 58 < (34175 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 58 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 58 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 58 +
      (4451662 / 100000000) * (-96 / 100) ^ 58 +
      (2545398 / 100000000) * (88 / 100) ^ 58 +
      (-4932634 / 100000000) * (95 / 100) ^ 58 +
      (11618157 / 100000000) * (984 / 1000) ^ 58 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 58 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 58 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 58 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 58 : ℚ) ^ 2 / 58) <
      34175 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 58 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_59 :
    barrierV2 59 ^ 2 / 59 < (224355 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 59 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 59 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 59 +
      (4451662 / 100000000) * (-96 / 100) ^ 59 +
      (2545398 / 100000000) * (88 / 100) ^ 59 +
      (-4932634 / 100000000) * (95 / 100) ^ 59 +
      (11618157 / 100000000) * (984 / 1000) ^ 59 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 59 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 59 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 59 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 59 : ℚ) ^ 2 / 59) <
      224355 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 59 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_60 :
    barrierV2 60 ^ 2 / 60 < (39602 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 60 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 60 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 60 +
      (4451662 / 100000000) * (-96 / 100) ^ 60 +
      (2545398 / 100000000) * (88 / 100) ^ 60 +
      (-4932634 / 100000000) * (95 / 100) ^ 60 +
      (11618157 / 100000000) * (984 / 1000) ^ 60 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 60 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 60 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 60 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 60 : ℚ) ^ 2 / 60) <
      39602 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 60 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_61 :
    barrierV2 61 ^ 2 / 61 < (22318 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 61 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 61 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 61 +
      (4451662 / 100000000) * (-96 / 100) ^ 61 +
      (2545398 / 100000000) * (88 / 100) ^ 61 +
      (-4932634 / 100000000) * (95 / 100) ^ 61 +
      (11618157 / 100000000) * (984 / 1000) ^ 61 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 61 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 61 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 61 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 61 : ℚ) ^ 2 / 61) <
      22318 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 61 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_62 :
    barrierV2 62 ^ 2 / 62 < (27101 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 62 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 62 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 62 +
      (4451662 / 100000000) * (-96 / 100) ^ 62 +
      (2545398 / 100000000) * (88 / 100) ^ 62 +
      (-4932634 / 100000000) * (95 / 100) ^ 62 +
      (11618157 / 100000000) * (984 / 1000) ^ 62 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 62 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 62 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 62 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 62 : ℚ) ^ 2 / 62) <
      27101 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 62 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_63 :
    barrierV2 63 ^ 2 / 63 < (189173 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 63 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 63 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 63 +
      (4451662 / 100000000) * (-96 / 100) ^ 63 +
      (2545398 / 100000000) * (88 / 100) ^ 63 +
      (-4932634 / 100000000) * (95 / 100) ^ 63 +
      (11618157 / 100000000) * (984 / 1000) ^ 63 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 63 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 63 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 63 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 63 : ℚ) ^ 2 / 63) <
      189173 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 63 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_64 :
    barrierV2 64 ^ 2 / 64 < (33410 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 64 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 64 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 64 +
      (4451662 / 100000000) * (-96 / 100) ^ 64 +
      (2545398 / 100000000) * (88 / 100) ^ 64 +
      (-4932634 / 100000000) * (95 / 100) ^ 64 +
      (11618157 / 100000000) * (984 / 1000) ^ 64 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 64 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 64 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 64 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 64 : ℚ) ^ 2 / 64) <
      33410 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 64 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_64 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (56 + k + 1) ^ 2 / ((56 + k + 1 : ℕ) : ℝ)) ≤
      (597308 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_57.le) barrierV2_norm_term_58.le) barrierV2_norm_term_59.le) barrierV2_norm_term_60.le) barrierV2_norm_term_61.le) barrierV2_norm_term_62.le) barrierV2_norm_term_63.le) barrierV2_norm_term_64.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_64 :
    (∑ k ∈ Finset.range 64,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1290163878 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (56 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_56 barrierV2_norm_block_64
  have hc : (1289566570 / 1000000000 : ℝ) + 597308 / 1000000000 =
      1290163878 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_65 :
    barrierV2 65 ^ 2 / 65 < (18446 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 65 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 65 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 65 +
      (4451662 / 100000000) * (-96 / 100) ^ 65 +
      (2545398 / 100000000) * (88 / 100) ^ 65 +
      (-4932634 / 100000000) * (95 / 100) ^ 65 +
      (11618157 / 100000000) * (984 / 1000) ^ 65 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 65 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 65 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 65 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 65 : ℚ) ^ 2 / 65) <
      18446 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 65 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_66 :
    barrierV2 66 ^ 2 / 66 < (21684 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 66 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 66 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 66 +
      (4451662 / 100000000) * (-96 / 100) ^ 66 +
      (2545398 / 100000000) * (88 / 100) ^ 66 +
      (-4932634 / 100000000) * (95 / 100) ^ 66 +
      (11618157 / 100000000) * (984 / 1000) ^ 66 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 66 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 66 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 66 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 66 : ℚ) ^ 2 / 66) <
      21684 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 66 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_67 :
    barrierV2 67 ^ 2 / 67 < (159780 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 67 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 67 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 67 +
      (4451662 / 100000000) * (-96 / 100) ^ 67 +
      (2545398 / 100000000) * (88 / 100) ^ 67 +
      (-4932634 / 100000000) * (95 / 100) ^ 67 +
      (11618157 / 100000000) * (984 / 1000) ^ 67 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 67 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 67 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 67 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 67 : ℚ) ^ 2 / 67) <
      159780 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 67 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_68 :
    barrierV2 68 ^ 2 / 68 < (28167 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 68 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 68 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 68 +
      (4451662 / 100000000) * (-96 / 100) ^ 68 +
      (2545398 / 100000000) * (88 / 100) ^ 68 +
      (-4932634 / 100000000) * (95 / 100) ^ 68 +
      (11618157 / 100000000) * (984 / 1000) ^ 68 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 68 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 68 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 68 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 68 : ℚ) ^ 2 / 68) <
      28167 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 68 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_69 :
    barrierV2 69 ^ 2 / 69 < (15321 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 69 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 69 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 69 +
      (4451662 / 100000000) * (-96 / 100) ^ 69 +
      (2545398 / 100000000) * (88 / 100) ^ 69 +
      (-4932634 / 100000000) * (95 / 100) ^ 69 +
      (11618157 / 100000000) * (984 / 1000) ^ 69 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 69 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 69 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 69 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 69 : ℚ) ^ 2 / 69) <
      15321 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 69 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_70 :
    barrierV2 70 ^ 2 / 70 < (17482 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 70 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 70 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 70 +
      (4451662 / 100000000) * (-96 / 100) ^ 70 +
      (2545398 / 100000000) * (88 / 100) ^ 70 +
      (-4932634 / 100000000) * (95 / 100) ^ 70 +
      (11618157 / 100000000) * (984 / 1000) ^ 70 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 70 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 70 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 70 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 70 : ℚ) ^ 2 / 70) <
      17482 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 70 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_71 :
    barrierV2 71 ^ 2 / 71 < (135138 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 71 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 71 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 71 +
      (4451662 / 100000000) * (-96 / 100) ^ 71 +
      (2545398 / 100000000) * (88 / 100) ^ 71 +
      (-4932634 / 100000000) * (95 / 100) ^ 71 +
      (11618157 / 100000000) * (984 / 1000) ^ 71 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 71 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 71 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 71 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 71 : ℚ) ^ 2 / 71) <
      135138 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 71 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_72 :
    barrierV2 72 ^ 2 / 72 < (23745 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 72 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 72 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 72 +
      (4451662 / 100000000) * (-96 / 100) ^ 72 +
      (2545398 / 100000000) * (88 / 100) ^ 72 +
      (-4932634 / 100000000) * (95 / 100) ^ 72 +
      (11618157 / 100000000) * (984 / 1000) ^ 72 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 72 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 72 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 72 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 72 : ℚ) ^ 2 / 72) <
      23745 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 72 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_72 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (64 + k + 1) ^ 2 / ((64 + k + 1 : ℕ) : ℝ)) ≤
      (419763 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_65.le) barrierV2_norm_term_66.le) barrierV2_norm_term_67.le) barrierV2_norm_term_68.le) barrierV2_norm_term_69.le) barrierV2_norm_term_70.le) barrierV2_norm_term_71.le) barrierV2_norm_term_72.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_72 :
    (∑ k ∈ Finset.range 72,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1290583641 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (64 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_64 barrierV2_norm_block_72
  have hc : (1290163878 / 1000000000 : ℝ) + 419763 / 1000000000 =
      1290583641 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_73 :
    barrierV2 73 ^ 2 / 73 < (12775 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 73 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 73 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 73 +
      (4451662 / 100000000) * (-96 / 100) ^ 73 +
      (2545398 / 100000000) * (88 / 100) ^ 73 +
      (-4932634 / 100000000) * (95 / 100) ^ 73 +
      (11618157 / 100000000) * (984 / 1000) ^ 73 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 73 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 73 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 73 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 73 : ℚ) ^ 2 / 73) <
      12775 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 73 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_74 :
    barrierV2 74 ^ 2 / 74 < (14186 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 74 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 74 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 74 +
      (4451662 / 100000000) * (-96 / 100) ^ 74 +
      (2545398 / 100000000) * (88 / 100) ^ 74 +
      (-4932634 / 100000000) * (95 / 100) ^ 74 +
      (11618157 / 100000000) * (984 / 1000) ^ 74 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 74 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 74 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 74 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 74 : ℚ) ^ 2 / 74) <
      14186 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 74 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_75 :
    barrierV2 75 ^ 2 / 75 < (114425 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 75 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 75 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 75 +
      (4451662 / 100000000) * (-96 / 100) ^ 75 +
      (2545398 / 100000000) * (88 / 100) ^ 75 +
      (-4932634 / 100000000) * (95 / 100) ^ 75 +
      (11618157 / 100000000) * (984 / 1000) ^ 75 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 75 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 75 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 75 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 75 : ℚ) ^ 2 / 75) <
      114425 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 75 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_76 :
    barrierV2 76 ^ 2 / 76 < (20022 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 76 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 76 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 76 +
      (4451662 / 100000000) * (-96 / 100) ^ 76 +
      (2545398 / 100000000) * (88 / 100) ^ 76 +
      (-4932634 / 100000000) * (95 / 100) ^ 76 +
      (11618157 / 100000000) * (984 / 1000) ^ 76 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 76 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 76 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 76 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 76 : ℚ) ^ 2 / 76) <
      20022 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 76 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_77 :
    barrierV2 77 ^ 2 / 77 < (10687 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 77 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 77 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 77 +
      (4451662 / 100000000) * (-96 / 100) ^ 77 +
      (2545398 / 100000000) * (88 / 100) ^ 77 +
      (-4932634 / 100000000) * (95 / 100) ^ 77 +
      (11618157 / 100000000) * (984 / 1000) ^ 77 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 77 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 77 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 77 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 77 : ℚ) ^ 2 / 77) <
      10687 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 77 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_78 :
    barrierV2 78 ^ 2 / 78 < (11577 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 78 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 78 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 78 +
      (4451662 / 100000000) * (-96 / 100) ^ 78 +
      (2545398 / 100000000) * (88 / 100) ^ 78 +
      (-4932634 / 100000000) * (95 / 100) ^ 78 +
      (11618157 / 100000000) * (984 / 1000) ^ 78 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 78 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 78 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 78 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 78 : ℚ) ^ 2 / 78) <
      11577 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 78 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_79 :
    barrierV2 79 ^ 2 / 79 < (96981 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 79 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 79 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 79 +
      (4451662 / 100000000) * (-96 / 100) ^ 79 +
      (2545398 / 100000000) * (88 / 100) ^ 79 +
      (-4932634 / 100000000) * (95 / 100) ^ 79 +
      (11618157 / 100000000) * (984 / 1000) ^ 79 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 79 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 79 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 79 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 79 : ℚ) ^ 2 / 79) <
      96981 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 79 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_80 :
    barrierV2 80 ^ 2 / 80 < (16892 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 80 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 80 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 80 +
      (4451662 / 100000000) * (-96 / 100) ^ 80 +
      (2545398 / 100000000) * (88 / 100) ^ 80 +
      (-4932634 / 100000000) * (95 / 100) ^ 80 +
      (11618157 / 100000000) * (984 / 1000) ^ 80 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 80 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 80 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 80 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 80 : ℚ) ^ 2 / 80) <
      16892 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 80 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_80 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (72 + k + 1) ^ 2 / ((72 + k + 1 : ℕ) : ℝ)) ≤
      (297545 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_73.le) barrierV2_norm_term_74.le) barrierV2_norm_term_75.le) barrierV2_norm_term_76.le) barrierV2_norm_term_77.le) barrierV2_norm_term_78.le) barrierV2_norm_term_79.le) barrierV2_norm_term_80.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_80 :
    (∑ k ∈ Finset.range 80,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1290881186 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (72 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_72 barrierV2_norm_block_80
  have hc : (1290583641 / 1000000000 : ℝ) + 297545 / 1000000000 =
      1290881186 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_81 :
    barrierV2 81 ^ 2 / 81 < (8964 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 81 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 81 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 81 +
      (4451662 / 100000000) * (-96 / 100) ^ 81 +
      (2545398 / 100000000) * (88 / 100) ^ 81 +
      (-4932634 / 100000000) * (95 / 100) ^ 81 +
      (11618157 / 100000000) * (984 / 1000) ^ 81 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 81 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 81 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 81 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 81 : ℚ) ^ 2 / 81) <
      8964 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 81 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_82 :
    barrierV2 82 ^ 2 / 82 < (9494 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 82 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 82 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 82 +
      (4451662 / 100000000) * (-96 / 100) ^ 82 +
      (2545398 / 100000000) * (88 / 100) ^ 82 +
      (-4932634 / 100000000) * (95 / 100) ^ 82 +
      (11618157 / 100000000) * (984 / 1000) ^ 82 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 82 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 82 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 82 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 82 : ℚ) ^ 2 / 82) <
      9494 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 82 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_83 :
    barrierV2 83 ^ 2 / 83 < (82268 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 83 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 83 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 83 +
      (4451662 / 100000000) * (-96 / 100) ^ 83 +
      (2545398 / 100000000) * (88 / 100) ^ 83 +
      (-4932634 / 100000000) * (95 / 100) ^ 83 +
      (11618157 / 100000000) * (984 / 1000) ^ 83 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 83 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 83 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 83 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 83 : ℚ) ^ 2 / 83) <
      82268 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 83 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_84 :
    barrierV2 84 ^ 2 / 84 < (14261 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 84 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 84 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 84 +
      (4451662 / 100000000) * (-96 / 100) ^ 84 +
      (2545398 / 100000000) * (88 / 100) ^ 84 +
      (-4932634 / 100000000) * (95 / 100) ^ 84 +
      (11618157 / 100000000) * (984 / 1000) ^ 84 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 84 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 84 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 84 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 84 : ℚ) ^ 2 / 84) <
      14261 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 84 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_85 :
    barrierV2 85 ^ 2 / 85 < (7536 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 85 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 85 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 85 +
      (4451662 / 100000000) * (-96 / 100) ^ 85 +
      (2545398 / 100000000) * (88 / 100) ^ 85 +
      (-4932634 / 100000000) * (95 / 100) ^ 85 +
      (11618157 / 100000000) * (984 / 1000) ^ 85 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 85 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 85 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 85 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 85 : ℚ) ^ 2 / 85) <
      7536 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 85 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_86 :
    barrierV2 86 ^ 2 / 86 < (7820 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 86 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 86 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 86 +
      (4451662 / 100000000) * (-96 / 100) ^ 86 +
      (2545398 / 100000000) * (88 / 100) ^ 86 +
      (-4932634 / 100000000) * (95 / 100) ^ 86 +
      (11618157 / 100000000) * (984 / 1000) ^ 86 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 86 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 86 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 86 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 86 : ℚ) ^ 2 / 86) <
      7820 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 86 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_87 :
    barrierV2 87 ^ 2 / 87 < (69843 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 87 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 87 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 87 +
      (4451662 / 100000000) * (-96 / 100) ^ 87 +
      (2545398 / 100000000) * (88 / 100) ^ 87 +
      (-4932634 / 100000000) * (95 / 100) ^ 87 +
      (11618157 / 100000000) * (984 / 1000) ^ 87 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 87 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 87 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 87 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 87 : ℚ) ^ 2 / 87) <
      69843 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 87 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_88 :
    barrierV2 88 ^ 2 / 88 < (12050 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 88 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 88 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 88 +
      (4451662 / 100000000) * (-96 / 100) ^ 88 +
      (2545398 / 100000000) * (88 / 100) ^ 88 +
      (-4932634 / 100000000) * (95 / 100) ^ 88 +
      (11618157 / 100000000) * (984 / 1000) ^ 88 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 88 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 88 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 88 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 88 : ℚ) ^ 2 / 88) <
      12050 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 88 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_88 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (80 + k + 1) ^ 2 / ((80 + k + 1 : ℕ) : ℝ)) ≤
      (212236 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_81.le) barrierV2_norm_term_82.le) barrierV2_norm_term_83.le) barrierV2_norm_term_84.le) barrierV2_norm_term_85.le) barrierV2_norm_term_86.le) barrierV2_norm_term_87.le) barrierV2_norm_term_88.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_88 :
    (∑ k ∈ Finset.range 88,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291093422 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (80 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_80 barrierV2_norm_block_88
  have hc : (1290881186 / 1000000000 : ℝ) + 212236 / 1000000000 =
      1291093422 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_89 :
    barrierV2 89 ^ 2 / 89 < (6348 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 89 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 89 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 89 +
      (4451662 / 100000000) * (-96 / 100) ^ 89 +
      (2545398 / 100000000) * (88 / 100) ^ 89 +
      (-4932634 / 100000000) * (95 / 100) ^ 89 +
      (11618157 / 100000000) * (984 / 1000) ^ 89 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 89 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 89 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 89 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 89 : ℚ) ^ 2 / 89) <
      6348 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 89 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_90 :
    barrierV2 90 ^ 2 / 90 < (6466 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 90 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 90 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 90 +
      (4451662 / 100000000) * (-96 / 100) ^ 90 +
      (2545398 / 100000000) * (88 / 100) ^ 90 +
      (-4932634 / 100000000) * (95 / 100) ^ 90 +
      (11618157 / 100000000) * (984 / 1000) ^ 90 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 90 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 90 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 90 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 90 : ℚ) ^ 2 / 90) <
      6466 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 90 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_91 :
    barrierV2 91 ^ 2 / 91 < (59338 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 91 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 91 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 91 +
      (4451662 / 100000000) * (-96 / 100) ^ 91 +
      (2545398 / 100000000) * (88 / 100) ^ 91 +
      (-4932634 / 100000000) * (95 / 100) ^ 91 +
      (11618157 / 100000000) * (984 / 1000) ^ 91 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 91 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 91 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 91 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 91 : ℚ) ^ 2 / 91) <
      59338 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 91 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_92 :
    barrierV2 92 ^ 2 / 92 < (10190 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 92 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 92 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 92 +
      (4451662 / 100000000) * (-96 / 100) ^ 92 +
      (2545398 / 100000000) * (88 / 100) ^ 92 +
      (-4932634 / 100000000) * (95 / 100) ^ 92 +
      (11618157 / 100000000) * (984 / 1000) ^ 92 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 92 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 92 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 92 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 92 : ℚ) ^ 2 / 92) <
      10190 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 92 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_93 :
    barrierV2 93 ^ 2 / 93 < (5357 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 93 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 93 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 93 +
      (4451662 / 100000000) * (-96 / 100) ^ 93 +
      (2545398 / 100000000) * (88 / 100) ^ 93 +
      (-4932634 / 100000000) * (95 / 100) ^ 93 +
      (11618157 / 100000000) * (984 / 1000) ^ 93 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 93 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 93 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 93 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 93 : ℚ) ^ 2 / 93) <
      5357 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 93 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_94 :
    barrierV2 94 ^ 2 / 94 < (5365 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 94 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 94 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 94 +
      (4451662 / 100000000) * (-96 / 100) ^ 94 +
      (2545398 / 100000000) * (88 / 100) ^ 94 +
      (-4932634 / 100000000) * (95 / 100) ^ 94 +
      (11618157 / 100000000) * (984 / 1000) ^ 94 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 94 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 94 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 94 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 94 : ℚ) ^ 2 / 94) <
      5365 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 94 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_95 :
    barrierV2 95 ^ 2 / 95 < (50450 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 95 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 95 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 95 +
      (4451662 / 100000000) * (-96 / 100) ^ 95 +
      (2545398 / 100000000) * (88 / 100) ^ 95 +
      (-4932634 / 100000000) * (95 / 100) ^ 95 +
      (11618157 / 100000000) * (984 / 1000) ^ 95 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 95 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 95 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 95 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 95 : ℚ) ^ 2 / 95) <
      50450 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 95 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_96 :
    barrierV2 96 ^ 2 / 96 < (8626 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 96 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 96 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 96 +
      (4451662 / 100000000) * (-96 / 100) ^ 96 +
      (2545398 / 100000000) * (88 / 100) ^ 96 +
      (-4932634 / 100000000) * (95 / 100) ^ 96 +
      (11618157 / 100000000) * (984 / 1000) ^ 96 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 96 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 96 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 96 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 96 : ℚ) ^ 2 / 96) <
      8626 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 96 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_96 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (88 + k + 1) ^ 2 / ((88 + k + 1 : ℕ) : ℝ)) ≤
      (152140 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_89.le) barrierV2_norm_term_90.le) barrierV2_norm_term_91.le) barrierV2_norm_term_92.le) barrierV2_norm_term_93.le) barrierV2_norm_term_94.le) barrierV2_norm_term_95.le) barrierV2_norm_term_96.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_96 :
    (∑ k ∈ Finset.range 96,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291245562 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (88 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_88 barrierV2_norm_block_96
  have hc : (1291093422 / 1000000000 : ℝ) + 152140 / 1000000000 =
      1291245562 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end

end OAI
