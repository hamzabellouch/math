import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import OAI.NumberTheory.Catalan.Energy.BarrierTwoNormVPrefix096

namespace OAI


noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_97 :
    barrierV2 97 ^ 2 / 97 < (4527 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 97 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 97 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 97 +
      (4451662 / 100000000) * (-96 / 100) ^ 97 +
      (2545398 / 100000000) * (88 / 100) ^ 97 +
      (-4932634 / 100000000) * (95 / 100) ^ 97 +
      (11618157 / 100000000) * (984 / 1000) ^ 97 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 97 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 97 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 97 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 97 : ℚ) ^ 2 / 97) <
      4527 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 97 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_98 :
    barrierV2 98 ^ 2 / 98 < (4466 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 98 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 98 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 98 +
      (4451662 / 100000000) * (-96 / 100) ^ 98 +
      (2545398 / 100000000) * (88 / 100) ^ 98 +
      (-4932634 / 100000000) * (95 / 100) ^ 98 +
      (11618157 / 100000000) * (984 / 1000) ^ 98 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 98 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 98 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 98 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 98 : ℚ) ^ 2 / 98) <
      4466 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 98 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_99 :
    barrierV2 99 ^ 2 / 99 < (42922 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 99 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 99 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 99 +
      (4451662 / 100000000) * (-96 / 100) ^ 99 +
      (2545398 / 100000000) * (88 / 100) ^ 99 +
      (-4932634 / 100000000) * (95 / 100) ^ 99 +
      (11618157 / 100000000) * (984 / 1000) ^ 99 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 99 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 99 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 99 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 99 : ℚ) ^ 2 / 99) <
      42922 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 99 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_100 :
    barrierV2 100 ^ 2 / 100 < (7308 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 100 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 100 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 100 +
      (4451662 / 100000000) * (-96 / 100) ^ 100 +
      (2545398 / 100000000) * (88 / 100) ^ 100 +
      (-4932634 / 100000000) * (95 / 100) ^ 100 +
      (11618157 / 100000000) * (984 / 1000) ^ 100 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 100 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 100 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 100 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 100 : ℚ) ^ 2 / 100) <
      7308 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 100 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_101 :
    barrierV2 101 ^ 2 / 101 < (3831 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 101 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 101 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 101 +
      (4451662 / 100000000) * (-96 / 100) ^ 101 +
      (2545398 / 100000000) * (88 / 100) ^ 101 +
      (-4932634 / 100000000) * (95 / 100) ^ 101 +
      (11618157 / 100000000) * (984 / 1000) ^ 101 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 101 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 101 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 101 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 101 : ℚ) ^ 2 / 101) <
      3831 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 101 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_102 :
    barrierV2 102 ^ 2 / 102 < (3729 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 102 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 102 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 102 +
      (4451662 / 100000000) * (-96 / 100) ^ 102 +
      (2545398 / 100000000) * (88 / 100) ^ 102 +
      (-4932634 / 100000000) * (95 / 100) ^ 102 +
      (11618157 / 100000000) * (984 / 1000) ^ 102 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 102 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 102 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 102 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 102 : ℚ) ^ 2 / 102) <
      3729 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 102 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_103 :
    barrierV2 103 ^ 2 / 103 < (36542 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 103 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 103 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 103 +
      (4451662 / 100000000) * (-96 / 100) ^ 103 +
      (2545398 / 100000000) * (88 / 100) ^ 103 +
      (-4932634 / 100000000) * (95 / 100) ^ 103 +
      (11618157 / 100000000) * (984 / 1000) ^ 103 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 103 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 103 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 103 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 103 : ℚ) ^ 2 / 103) <
      36542 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 103 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_104 :
    barrierV2 104 ^ 2 / 104 < (6197 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 104 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 104 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 104 +
      (4451662 / 100000000) * (-96 / 100) ^ 104 +
      (2545398 / 100000000) * (88 / 100) ^ 104 +
      (-4932634 / 100000000) * (95 / 100) ^ 104 +
      (11618157 / 100000000) * (984 / 1000) ^ 104 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 104 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 104 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 104 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 104 : ℚ) ^ 2 / 104) <
      6197 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 104 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_104 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (96 + k + 1) ^ 2 / ((96 + k + 1 : ℕ) : ℝ)) ≤
      (109522 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_97.le) barrierV2_norm_term_98.le) barrierV2_norm_term_99.le) barrierV2_norm_term_100.le) barrierV2_norm_term_101.le) barrierV2_norm_term_102.le) barrierV2_norm_term_103.le) barrierV2_norm_term_104.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_104 :
    (∑ k ∈ Finset.range 104,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291355084 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (96 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_96 barrierV2_norm_block_104
  have hc : (1291245562 / 1000000000 : ℝ) + 109522 / 1000000000 =
      1291355084 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_105 :
    barrierV2 105 ^ 2 / 105 < (3246 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 105 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 105 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 105 +
      (4451662 / 100000000) * (-96 / 100) ^ 105 +
      (2545398 / 100000000) * (88 / 100) ^ 105 +
      (-4932634 / 100000000) * (95 / 100) ^ 105 +
      (11618157 / 100000000) * (984 / 1000) ^ 105 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 105 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 105 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 105 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 105 : ℚ) ^ 2 / 105) <
      3246 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 105 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_106 :
    barrierV2 106 ^ 2 / 106 < (3121 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 106 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 106 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 106 +
      (4451662 / 100000000) * (-96 / 100) ^ 106 +
      (2545398 / 100000000) * (88 / 100) ^ 106 +
      (-4932634 / 100000000) * (95 / 100) ^ 106 +
      (11618157 / 100000000) * (984 / 1000) ^ 106 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 106 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 106 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 106 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 106 : ℚ) ^ 2 / 106) <
      3121 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 106 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_107 :
    barrierV2 107 ^ 2 / 107 < (31130 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 107 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 107 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 107 +
      (4451662 / 100000000) * (-96 / 100) ^ 107 +
      (2545398 / 100000000) * (88 / 100) ^ 107 +
      (-4932634 / 100000000) * (95 / 100) ^ 107 +
      (11618157 / 100000000) * (984 / 1000) ^ 107 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 107 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 107 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 107 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 107 : ℚ) ^ 2 / 107) <
      31130 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 107 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_108 :
    barrierV2 108 ^ 2 / 108 < (5260 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 108 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 108 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 108 +
      (4451662 / 100000000) * (-96 / 100) ^ 108 +
      (2545398 / 100000000) * (88 / 100) ^ 108 +
      (-4932634 / 100000000) * (95 / 100) ^ 108 +
      (11618157 / 100000000) * (984 / 1000) ^ 108 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 108 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 108 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 108 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 108 : ℚ) ^ 2 / 108) <
      5260 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 108 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_109 :
    barrierV2 109 ^ 2 / 109 < (2754 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 109 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 109 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 109 +
      (4451662 / 100000000) * (-96 / 100) ^ 109 +
      (2545398 / 100000000) * (88 / 100) ^ 109 +
      (-4932634 / 100000000) * (95 / 100) ^ 109 +
      (11618157 / 100000000) * (984 / 1000) ^ 109 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 109 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 109 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 109 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 109 : ℚ) ^ 2 / 109) <
      2754 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 109 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_110 :
    barrierV2 110 ^ 2 / 110 < (2619 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 110 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 110 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 110 +
      (4451662 / 100000000) * (-96 / 100) ^ 110 +
      (2545398 / 100000000) * (88 / 100) ^ 110 +
      (-4932634 / 100000000) * (95 / 100) ^ 110 +
      (11618157 / 100000000) * (984 / 1000) ^ 110 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 110 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 110 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 110 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 110 : ℚ) ^ 2 / 110) <
      2619 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 110 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_111 :
    barrierV2 111 ^ 2 / 111 < (26537 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 111 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 111 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 111 +
      (4451662 / 100000000) * (-96 / 100) ^ 111 +
      (2545398 / 100000000) * (88 / 100) ^ 111 +
      (-4932634 / 100000000) * (95 / 100) ^ 111 +
      (11618157 / 100000000) * (984 / 1000) ^ 111 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 111 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 111 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 111 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 111 : ℚ) ^ 2 / 111) <
      26537 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 111 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_112 :
    barrierV2 112 ^ 2 / 112 < (4469 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 112 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 112 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 112 +
      (4451662 / 100000000) * (-96 / 100) ^ 112 +
      (2545398 / 100000000) * (88 / 100) ^ 112 +
      (-4932634 / 100000000) * (95 / 100) ^ 112 +
      (11618157 / 100000000) * (984 / 1000) ^ 112 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 112 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 112 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 112 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 112 : ℚ) ^ 2 / 112) <
      4469 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 112 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_112 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (104 + k + 1) ^ 2 / ((104 + k + 1 : ℕ) : ℝ)) ≤
      (79136 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_105.le) barrierV2_norm_term_106.le) barrierV2_norm_term_107.le) barrierV2_norm_term_108.le) barrierV2_norm_term_109.le) barrierV2_norm_term_110.le) barrierV2_norm_term_111.le) barrierV2_norm_term_112.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_112 :
    (∑ k ∈ Finset.range 112,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291434220 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (104 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_104 barrierV2_norm_block_112
  have hc : (1291355084 / 1000000000 : ℝ) + 79136 / 1000000000 =
      1291434220 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_113 :
    barrierV2 113 ^ 2 / 113 < (2339 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 113 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 113 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 113 +
      (4451662 / 100000000) * (-96 / 100) ^ 113 +
      (2545398 / 100000000) * (88 / 100) ^ 113 +
      (-4932634 / 100000000) * (95 / 100) ^ 113 +
      (11618157 / 100000000) * (984 / 1000) ^ 113 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 113 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 113 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 113 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 113 : ℚ) ^ 2 / 113) <
      2339 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 113 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_114 :
    barrierV2 114 ^ 2 / 114 < (2202 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 114 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 114 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 114 +
      (4451662 / 100000000) * (-96 / 100) ^ 114 +
      (2545398 / 100000000) * (88 / 100) ^ 114 +
      (-4932634 / 100000000) * (95 / 100) ^ 114 +
      (11618157 / 100000000) * (984 / 1000) ^ 114 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 114 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 114 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 114 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 114 : ℚ) ^ 2 / 114) <
      2202 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 114 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_115 :
    barrierV2 115 ^ 2 / 115 < (22636 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 115 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 115 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 115 +
      (4451662 / 100000000) * (-96 / 100) ^ 115 +
      (2545398 / 100000000) * (88 / 100) ^ 115 +
      (-4932634 / 100000000) * (95 / 100) ^ 115 +
      (11618157 / 100000000) * (984 / 1000) ^ 115 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 115 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 115 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 115 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 115 : ℚ) ^ 2 / 115) <
      22636 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 115 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_116 :
    barrierV2 116 ^ 2 / 116 < (3800 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 116 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 116 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 116 +
      (4451662 / 100000000) * (-96 / 100) ^ 116 +
      (2545398 / 100000000) * (88 / 100) ^ 116 +
      (-4932634 / 100000000) * (95 / 100) ^ 116 +
      (11618157 / 100000000) * (984 / 1000) ^ 116 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 116 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 116 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 116 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 116 : ℚ) ^ 2 / 116) <
      3800 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 116 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_117 :
    barrierV2 117 ^ 2 / 117 < (1989 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 117 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 117 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 117 +
      (4451662 / 100000000) * (-96 / 100) ^ 117 +
      (2545398 / 100000000) * (88 / 100) ^ 117 +
      (-4932634 / 100000000) * (95 / 100) ^ 117 +
      (11618157 / 100000000) * (984 / 1000) ^ 117 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 117 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 117 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 117 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 117 : ℚ) ^ 2 / 117) <
      1989 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 117 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_118 :
    barrierV2 118 ^ 2 / 118 < (1855 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 118 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 118 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 118 +
      (4451662 / 100000000) * (-96 / 100) ^ 118 +
      (2545398 / 100000000) * (88 / 100) ^ 118 +
      (-4932634 / 100000000) * (95 / 100) ^ 118 +
      (11618157 / 100000000) * (984 / 1000) ^ 118 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 118 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 118 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 118 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 118 : ℚ) ^ 2 / 118) <
      1855 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 118 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_119 :
    barrierV2 119 ^ 2 / 119 < (19320 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 119 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 119 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 119 +
      (4451662 / 100000000) * (-96 / 100) ^ 119 +
      (2545398 / 100000000) * (88 / 100) ^ 119 +
      (-4932634 / 100000000) * (95 / 100) ^ 119 +
      (11618157 / 100000000) * (984 / 1000) ^ 119 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 119 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 119 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 119 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 119 : ℚ) ^ 2 / 119) <
      19320 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 119 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_120 :
    barrierV2 120 ^ 2 / 120 < (3234 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 120 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 120 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 120 +
      (4451662 / 100000000) * (-96 / 100) ^ 120 +
      (2545398 / 100000000) * (88 / 100) ^ 120 +
      (-4932634 / 100000000) * (95 / 100) ^ 120 +
      (11618157 / 100000000) * (984 / 1000) ^ 120 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 120 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 120 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 120 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 120 : ℚ) ^ 2 / 120) <
      3234 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 120 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_120 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (112 + k + 1) ^ 2 / ((112 + k + 1 : ℕ) : ℝ)) ≤
      (57375 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_113.le) barrierV2_norm_term_114.le) barrierV2_norm_term_115.le) barrierV2_norm_term_116.le) barrierV2_norm_term_117.le) barrierV2_norm_term_118.le) barrierV2_norm_term_119.le) barrierV2_norm_term_120.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_120 :
    (∑ k ∈ Finset.range 120,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291491595 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (112 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_112 barrierV2_norm_block_120
  have hc : (1291434220 / 1000000000 : ℝ) + 57375 / 1000000000 =
      1291491595 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_121 :
    barrierV2 121 ^ 2 / 121 < (1692 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 121 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 121 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 121 +
      (4451662 / 100000000) * (-96 / 100) ^ 121 +
      (2545398 / 100000000) * (88 / 100) ^ 121 +
      (-4932634 / 100000000) * (95 / 100) ^ 121 +
      (11618157 / 100000000) * (984 / 1000) ^ 121 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 121 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 121 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 121 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 121 : ℚ) ^ 2 / 121) <
      1692 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 121 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_122 :
    barrierV2 122 ^ 2 / 122 < (1566 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 122 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 122 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 122 +
      (4451662 / 100000000) * (-96 / 100) ^ 122 +
      (2545398 / 100000000) * (88 / 100) ^ 122 +
      (-4932634 / 100000000) * (95 / 100) ^ 122 +
      (11618157 / 100000000) * (984 / 1000) ^ 122 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 122 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 122 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 122 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 122 : ℚ) ^ 2 / 122) <
      1566 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 122 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_123 :
    barrierV2 123 ^ 2 / 123 < (16499 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 123 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 123 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 123 +
      (4451662 / 100000000) * (-96 / 100) ^ 123 +
      (2545398 / 100000000) * (88 / 100) ^ 123 +
      (-4932634 / 100000000) * (95 / 100) ^ 123 +
      (11618157 / 100000000) * (984 / 1000) ^ 123 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 123 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 123 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 123 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 123 : ℚ) ^ 2 / 123) <
      16499 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 123 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_124 :
    barrierV2 124 ^ 2 / 124 < (2754 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 124 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 124 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 124 +
      (4451662 / 100000000) * (-96 / 100) ^ 124 +
      (2545398 / 100000000) * (88 / 100) ^ 124 +
      (-4932634 / 100000000) * (95 / 100) ^ 124 +
      (11618157 / 100000000) * (984 / 1000) ^ 124 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 124 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 124 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 124 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 124 : ℚ) ^ 2 / 124) <
      2754 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 124 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_125 :
    barrierV2 125 ^ 2 / 125 < (1442 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 125 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 125 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 125 +
      (4451662 / 100000000) * (-96 / 100) ^ 125 +
      (2545398 / 100000000) * (88 / 100) ^ 125 +
      (-4932634 / 100000000) * (95 / 100) ^ 125 +
      (11618157 / 100000000) * (984 / 1000) ^ 125 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 125 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 125 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 125 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 125 : ℚ) ^ 2 / 125) <
      1442 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 125 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_126 :
    barrierV2 126 ^ 2 / 126 < (1325 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 126 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 126 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 126 +
      (4451662 / 100000000) * (-96 / 100) ^ 126 +
      (2545398 / 100000000) * (88 / 100) ^ 126 +
      (-4932634 / 100000000) * (95 / 100) ^ 126 +
      (11618157 / 100000000) * (984 / 1000) ^ 126 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 126 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 126 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 126 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 126 : ℚ) ^ 2 / 126) <
      1325 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 126 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_127 :
    barrierV2 127 ^ 2 / 127 < (14099 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 127 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 127 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 127 +
      (4451662 / 100000000) * (-96 / 100) ^ 127 +
      (2545398 / 100000000) * (88 / 100) ^ 127 +
      (-4932634 / 100000000) * (95 / 100) ^ 127 +
      (11618157 / 100000000) * (984 / 1000) ^ 127 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 127 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 127 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 127 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 127 : ℚ) ^ 2 / 127) <
      14099 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 127 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_128 :
    barrierV2 128 ^ 2 / 128 < (2348 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 128 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 128 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 128 +
      (4451662 / 100000000) * (-96 / 100) ^ 128 +
      (2545398 / 100000000) * (88 / 100) ^ 128 +
      (-4932634 / 100000000) * (95 / 100) ^ 128 +
      (11618157 / 100000000) * (984 / 1000) ^ 128 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 128 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 128 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 128 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 128 : ℚ) ^ 2 / 128) <
      2348 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 128 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_128 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (120 + k + 1) ^ 2 / ((120 + k + 1 : ℕ) : ℝ)) ≤
      (41725 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_121.le) barrierV2_norm_term_122.le) barrierV2_norm_term_123.le) barrierV2_norm_term_124.le) barrierV2_norm_term_125.le) barrierV2_norm_term_126.le) barrierV2_norm_term_127.le) barrierV2_norm_term_128.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_128 :
    (∑ k ∈ Finset.range 128,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291533320 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (120 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_120 barrierV2_norm_block_128
  have hc : (1291491595 / 1000000000 : ℝ) + 41725 / 1000000000 =
      1291533320 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_129 :
    barrierV2 129 ^ 2 / 129 < (1229 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 129 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 129 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 129 +
      (4451662 / 100000000) * (-96 / 100) ^ 129 +
      (2545398 / 100000000) * (88 / 100) ^ 129 +
      (-4932634 / 100000000) * (95 / 100) ^ 129 +
      (11618157 / 100000000) * (984 / 1000) ^ 129 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 129 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 129 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 129 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 129 : ℚ) ^ 2 / 129) <
      1229 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 129 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_130 :
    barrierV2 130 ^ 2 / 130 < (1122 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 130 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 130 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 130 +
      (4451662 / 100000000) * (-96 / 100) ^ 130 +
      (2545398 / 100000000) * (88 / 100) ^ 130 +
      (-4932634 / 100000000) * (95 / 100) ^ 130 +
      (11618157 / 100000000) * (984 / 1000) ^ 130 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 130 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 130 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 130 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 130 : ℚ) ^ 2 / 130) <
      1122 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 130 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_131 :
    barrierV2 131 ^ 2 / 131 < (12054 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 131 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 131 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 131 +
      (4451662 / 100000000) * (-96 / 100) ^ 131 +
      (2545398 / 100000000) * (88 / 100) ^ 131 +
      (-4932634 / 100000000) * (95 / 100) ^ 131 +
      (11618157 / 100000000) * (984 / 1000) ^ 131 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 131 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 131 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 131 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 131 : ℚ) ^ 2 / 131) <
      12054 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 131 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_132 :
    barrierV2 132 ^ 2 / 132 < (2003 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 132 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 132 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 132 +
      (4451662 / 100000000) * (-96 / 100) ^ 132 +
      (2545398 / 100000000) * (88 / 100) ^ 132 +
      (-4932634 / 100000000) * (95 / 100) ^ 132 +
      (11618157 / 100000000) * (984 / 1000) ^ 132 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 132 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 132 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 132 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 132 : ℚ) ^ 2 / 132) <
      2003 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 132 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_133 :
    barrierV2 133 ^ 2 / 133 < (1049 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 133 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 133 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 133 +
      (4451662 / 100000000) * (-96 / 100) ^ 133 +
      (2545398 / 100000000) * (88 / 100) ^ 133 +
      (-4932634 / 100000000) * (95 / 100) ^ 133 +
      (11618157 / 100000000) * (984 / 1000) ^ 133 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 133 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 133 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 133 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 133 : ℚ) ^ 2 / 133) <
      1049 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 133 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_134 :
    barrierV2 134 ^ 2 / 134 < (952 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 134 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 134 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 134 +
      (4451662 / 100000000) * (-96 / 100) ^ 134 +
      (2545398 / 100000000) * (88 / 100) ^ 134 +
      (-4932634 / 100000000) * (95 / 100) ^ 134 +
      (11618157 / 100000000) * (984 / 1000) ^ 134 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 134 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 134 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 134 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 134 : ℚ) ^ 2 / 134) <
      952 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 134 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_135 :
    barrierV2 135 ^ 2 / 135 < (10312 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 135 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 135 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 135 +
      (4451662 / 100000000) * (-96 / 100) ^ 135 +
      (2545398 / 100000000) * (88 / 100) ^ 135 +
      (-4932634 / 100000000) * (95 / 100) ^ 135 +
      (11618157 / 100000000) * (984 / 1000) ^ 135 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 135 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 135 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 135 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 135 : ℚ) ^ 2 / 135) <
      10312 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 135 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_136 :
    barrierV2 136 ^ 2 / 136 < (1710 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 136 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 136 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 136 +
      (4451662 / 100000000) * (-96 / 100) ^ 136 +
      (2545398 / 100000000) * (88 / 100) ^ 136 +
      (-4932634 / 100000000) * (95 / 100) ^ 136 +
      (11618157 / 100000000) * (984 / 1000) ^ 136 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 136 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 136 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 136 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 136 : ℚ) ^ 2 / 136) <
      1710 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 136 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_136 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (128 + k + 1) ^ 2 / ((128 + k + 1 : ℕ) : ℝ)) ≤
      (30431 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_129.le) barrierV2_norm_term_130.le) barrierV2_norm_term_131.le) barrierV2_norm_term_132.le) barrierV2_norm_term_133.le) barrierV2_norm_term_134.le) barrierV2_norm_term_135.le) barrierV2_norm_term_136.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_136 :
    (∑ k ∈ Finset.range 136,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291563751 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (128 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_128 barrierV2_norm_block_136
  have hc : (1291533320 / 1000000000 : ℝ) + 30431 / 1000000000 =
      1291563751 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_137 :
    barrierV2 137 ^ 2 / 137 < (895 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 137 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 137 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 137 +
      (4451662 / 100000000) * (-96 / 100) ^ 137 +
      (2545398 / 100000000) * (88 / 100) ^ 137 +
      (-4932634 / 100000000) * (95 / 100) ^ 137 +
      (11618157 / 100000000) * (984 / 1000) ^ 137 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 137 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 137 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 137 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 137 : ℚ) ^ 2 / 137) <
      895 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 137 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_138 :
    barrierV2 138 ^ 2 / 138 < (809 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 138 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 138 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 138 +
      (4451662 / 100000000) * (-96 / 100) ^ 138 +
      (2545398 / 100000000) * (88 / 100) ^ 138 +
      (-4932634 / 100000000) * (95 / 100) ^ 138 +
      (11618157 / 100000000) * (984 / 1000) ^ 138 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 138 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 138 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 138 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 138 : ℚ) ^ 2 / 138) <
      809 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 138 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_139 :
    barrierV2 139 ^ 2 / 139 < (8827 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 139 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 139 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 139 +
      (4451662 / 100000000) * (-96 / 100) ^ 139 +
      (2545398 / 100000000) * (88 / 100) ^ 139 +
      (-4932634 / 100000000) * (95 / 100) ^ 139 +
      (11618157 / 100000000) * (984 / 1000) ^ 139 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 139 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 139 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 139 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 139 : ℚ) ^ 2 / 139) <
      8827 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 139 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_140 :
    barrierV2 140 ^ 2 / 140 < (1461 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 140 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 140 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 140 +
      (4451662 / 100000000) * (-96 / 100) ^ 140 +
      (2545398 / 100000000) * (88 / 100) ^ 140 +
      (-4932634 / 100000000) * (95 / 100) ^ 140 +
      (11618157 / 100000000) * (984 / 1000) ^ 140 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 140 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 140 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 140 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 140 : ℚ) ^ 2 / 140) <
      1461 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 140 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_141 :
    barrierV2 141 ^ 2 / 141 < (765 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 141 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 141 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 141 +
      (4451662 / 100000000) * (-96 / 100) ^ 141 +
      (2545398 / 100000000) * (88 / 100) ^ 141 +
      (-4932634 / 100000000) * (95 / 100) ^ 141 +
      (11618157 / 100000000) * (984 / 1000) ^ 141 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 141 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 141 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 141 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 141 : ℚ) ^ 2 / 141) <
      765 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 141 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_142 :
    barrierV2 142 ^ 2 / 142 < (688 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 142 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 142 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 142 +
      (4451662 / 100000000) * (-96 / 100) ^ 142 +
      (2545398 / 100000000) * (88 / 100) ^ 142 +
      (-4932634 / 100000000) * (95 / 100) ^ 142 +
      (11618157 / 100000000) * (984 / 1000) ^ 142 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 142 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 142 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 142 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 142 : ℚ) ^ 2 / 142) <
      688 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 142 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_143 :
    barrierV2 143 ^ 2 / 143 < (7559 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 143 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 143 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 143 +
      (4451662 / 100000000) * (-96 / 100) ^ 143 +
      (2545398 / 100000000) * (88 / 100) ^ 143 +
      (-4932634 / 100000000) * (95 / 100) ^ 143 +
      (11618157 / 100000000) * (984 / 1000) ^ 143 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 143 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 143 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 143 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 143 : ℚ) ^ 2 / 143) <
      7559 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 143 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_144 :
    barrierV2 144 ^ 2 / 144 < (1249 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 144 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 144 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 144 +
      (4451662 / 100000000) * (-96 / 100) ^ 144 +
      (2545398 / 100000000) * (88 / 100) ^ 144 +
      (-4932634 / 100000000) * (95 / 100) ^ 144 +
      (11618157 / 100000000) * (984 / 1000) ^ 144 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 144 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 144 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 144 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 144 : ℚ) ^ 2 / 144) <
      1249 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 144 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_144 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (136 + k + 1) ^ 2 / ((136 + k + 1 : ℕ) : ℝ)) ≤
      (22253 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_137.le) barrierV2_norm_term_138.le) barrierV2_norm_term_139.le) barrierV2_norm_term_140.le) barrierV2_norm_term_141.le) barrierV2_norm_term_142.le) barrierV2_norm_term_143.le) barrierV2_norm_term_144.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_144 :
    (∑ k ∈ Finset.range 144,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291586004 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (136 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_136 barrierV2_norm_block_144
  have hc : (1291563751 / 1000000000 : ℝ) + 22253 / 1000000000 =
      1291586004 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end

end OAI
