import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import OAI.NumberTheory.Catalan.Energy.BarrierTwoNormVPrefix144

namespace OAI


noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_145 :
    barrierV2 145 ^ 2 / 145 < (654 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 145 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 145 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 145 +
      (4451662 / 100000000) * (-96 / 100) ^ 145 +
      (2545398 / 100000000) * (88 / 100) ^ 145 +
      (-4932634 / 100000000) * (95 / 100) ^ 145 +
      (11618157 / 100000000) * (984 / 1000) ^ 145 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 145 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 145 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 145 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 145 : ℚ) ^ 2 / 145) <
      654 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 145 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_146 :
    barrierV2 146 ^ 2 / 146 < (586 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 146 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 146 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 146 +
      (4451662 / 100000000) * (-96 / 100) ^ 146 +
      (2545398 / 100000000) * (88 / 100) ^ 146 +
      (-4932634 / 100000000) * (95 / 100) ^ 146 +
      (11618157 / 100000000) * (984 / 1000) ^ 146 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 146 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 146 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 146 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 146 : ℚ) ^ 2 / 146) <
      586 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 146 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_147 :
    barrierV2 147 ^ 2 / 147 < (6477 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 147 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 147 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 147 +
      (4451662 / 100000000) * (-96 / 100) ^ 147 +
      (2545398 / 100000000) * (88 / 100) ^ 147 +
      (-4932634 / 100000000) * (95 / 100) ^ 147 +
      (11618157 / 100000000) * (984 / 1000) ^ 147 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 147 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 147 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 147 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 147 : ℚ) ^ 2 / 147) <
      6477 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 147 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_148 :
    barrierV2 148 ^ 2 / 148 < (1068 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 148 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 148 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 148 +
      (4451662 / 100000000) * (-96 / 100) ^ 148 +
      (2545398 / 100000000) * (88 / 100) ^ 148 +
      (-4932634 / 100000000) * (95 / 100) ^ 148 +
      (11618157 / 100000000) * (984 / 1000) ^ 148 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 148 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 148 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 148 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 148 : ℚ) ^ 2 / 148) <
      1068 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 148 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_149 :
    barrierV2 149 ^ 2 / 149 < (560 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 149 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 149 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 149 +
      (4451662 / 100000000) * (-96 / 100) ^ 149 +
      (2545398 / 100000000) * (88 / 100) ^ 149 +
      (-4932634 / 100000000) * (95 / 100) ^ 149 +
      (11618157 / 100000000) * (984 / 1000) ^ 149 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 149 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 149 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 149 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 149 : ℚ) ^ 2 / 149) <
      560 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 149 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_150 :
    barrierV2 150 ^ 2 / 150 < (499 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 150 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 150 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 150 +
      (4451662 / 100000000) * (-96 / 100) ^ 150 +
      (2545398 / 100000000) * (88 / 100) ^ 150 +
      (-4932634 / 100000000) * (95 / 100) ^ 150 +
      (11618157 / 100000000) * (984 / 1000) ^ 150 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 150 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 150 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 150 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 150 : ℚ) ^ 2 / 150) <
      499 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 150 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_151 :
    barrierV2 151 ^ 2 / 151 < (5553 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 151 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 151 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 151 +
      (4451662 / 100000000) * (-96 / 100) ^ 151 +
      (2545398 / 100000000) * (88 / 100) ^ 151 +
      (-4932634 / 100000000) * (95 / 100) ^ 151 +
      (11618157 / 100000000) * (984 / 1000) ^ 151 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 151 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 151 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 151 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 151 : ℚ) ^ 2 / 151) <
      5553 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 151 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_152 :
    barrierV2 152 ^ 2 / 152 < (915 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 152 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 152 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 152 +
      (4451662 / 100000000) * (-96 / 100) ^ 152 +
      (2545398 / 100000000) * (88 / 100) ^ 152 +
      (-4932634 / 100000000) * (95 / 100) ^ 152 +
      (11618157 / 100000000) * (984 / 1000) ^ 152 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 152 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 152 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 152 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 152 : ℚ) ^ 2 / 152) <
      915 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 152 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_152 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (144 + k + 1) ^ 2 / ((144 + k + 1 : ℕ) : ℝ)) ≤
      (16312 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_145.le) barrierV2_norm_term_146.le) barrierV2_norm_term_147.le) barrierV2_norm_term_148.le) barrierV2_norm_term_149.le) barrierV2_norm_term_150.le) barrierV2_norm_term_151.le) barrierV2_norm_term_152.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_152 :
    (∑ k ∈ Finset.range 152,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291602316 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (144 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_144 barrierV2_norm_block_152
  have hc : (1291586004 / 1000000000 : ℝ) + 16312 / 1000000000 =
      1291602316 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_153 :
    barrierV2 153 ^ 2 / 153 < (480 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 153 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 153 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 153 +
      (4451662 / 100000000) * (-96 / 100) ^ 153 +
      (2545398 / 100000000) * (88 / 100) ^ 153 +
      (-4932634 / 100000000) * (95 / 100) ^ 153 +
      (11618157 / 100000000) * (984 / 1000) ^ 153 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 153 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 153 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 153 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 153 : ℚ) ^ 2 / 153) <
      480 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 153 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_154 :
    barrierV2 154 ^ 2 / 154 < (426 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 154 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 154 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 154 +
      (4451662 / 100000000) * (-96 / 100) ^ 154 +
      (2545398 / 100000000) * (88 / 100) ^ 154 +
      (-4932634 / 100000000) * (95 / 100) ^ 154 +
      (11618157 / 100000000) * (984 / 1000) ^ 154 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 154 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 154 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 154 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 154 : ℚ) ^ 2 / 154) <
      426 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 154 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_155 :
    barrierV2 155 ^ 2 / 155 < (4763 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 155 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 155 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 155 +
      (4451662 / 100000000) * (-96 / 100) ^ 155 +
      (2545398 / 100000000) * (88 / 100) ^ 155 +
      (-4932634 / 100000000) * (95 / 100) ^ 155 +
      (11618157 / 100000000) * (984 / 1000) ^ 155 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 155 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 155 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 155 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 155 : ℚ) ^ 2 / 155) <
      4763 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 155 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_156 :
    barrierV2 156 ^ 2 / 156 < (784 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 156 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 156 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 156 +
      (4451662 / 100000000) * (-96 / 100) ^ 156 +
      (2545398 / 100000000) * (88 / 100) ^ 156 +
      (-4932634 / 100000000) * (95 / 100) ^ 156 +
      (11618157 / 100000000) * (984 / 1000) ^ 156 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 156 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 156 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 156 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 156 : ℚ) ^ 2 / 156) <
      784 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 156 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_157 :
    barrierV2 157 ^ 2 / 157 < (411 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 157 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 157 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 157 +
      (4451662 / 100000000) * (-96 / 100) ^ 157 +
      (2545398 / 100000000) * (88 / 100) ^ 157 +
      (-4932634 / 100000000) * (95 / 100) ^ 157 +
      (11618157 / 100000000) * (984 / 1000) ^ 157 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 157 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 157 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 157 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 157 : ℚ) ^ 2 / 157) <
      411 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 157 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_158 :
    barrierV2 158 ^ 2 / 158 < (364 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 158 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 158 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 158 +
      (4451662 / 100000000) * (-96 / 100) ^ 158 +
      (2545398 / 100000000) * (88 / 100) ^ 158 +
      (-4932634 / 100000000) * (95 / 100) ^ 158 +
      (11618157 / 100000000) * (984 / 1000) ^ 158 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 158 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 158 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 158 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 158 : ℚ) ^ 2 / 158) <
      364 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 158 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_159 :
    barrierV2 159 ^ 2 / 159 < (4087 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 159 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 159 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 159 +
      (4451662 / 100000000) * (-96 / 100) ^ 159 +
      (2545398 / 100000000) * (88 / 100) ^ 159 +
      (-4932634 / 100000000) * (95 / 100) ^ 159 +
      (11618157 / 100000000) * (984 / 1000) ^ 159 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 159 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 159 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 159 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 159 : ℚ) ^ 2 / 159) <
      4087 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 159 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_160 :
    barrierV2 160 ^ 2 / 160 < (672 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 160 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 160 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 160 +
      (4451662 / 100000000) * (-96 / 100) ^ 160 +
      (2545398 / 100000000) * (88 / 100) ^ 160 +
      (-4932634 / 100000000) * (95 / 100) ^ 160 +
      (11618157 / 100000000) * (984 / 1000) ^ 160 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 160 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 160 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 160 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 160 : ℚ) ^ 2 / 160) <
      672 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 160 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_160 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (152 + k + 1) ^ 2 / ((152 + k + 1 : ℕ) : ℝ)) ≤
      (11987 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_153.le) barrierV2_norm_term_154.le) barrierV2_norm_term_155.le) barrierV2_norm_term_156.le) barrierV2_norm_term_157.le) barrierV2_norm_term_158.le) barrierV2_norm_term_159.le) barrierV2_norm_term_160.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_160 :
    (∑ k ∈ Finset.range 160,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291614303 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (152 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_152 barrierV2_norm_block_160
  have hc : (1291602316 / 1000000000 : ℝ) + 11987 / 1000000000 =
      1291614303 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_161 :
    barrierV2 161 ^ 2 / 161 < (352 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 161 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 161 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 161 +
      (4451662 / 100000000) * (-96 / 100) ^ 161 +
      (2545398 / 100000000) * (88 / 100) ^ 161 +
      (-4932634 / 100000000) * (95 / 100) ^ 161 +
      (11618157 / 100000000) * (984 / 1000) ^ 161 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 161 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 161 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 161 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 161 : ℚ) ^ 2 / 161) <
      352 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 161 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_162 :
    barrierV2 162 ^ 2 / 162 < (311 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 162 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 162 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 162 +
      (4451662 / 100000000) * (-96 / 100) ^ 162 +
      (2545398 / 100000000) * (88 / 100) ^ 162 +
      (-4932634 / 100000000) * (95 / 100) ^ 162 +
      (11618157 / 100000000) * (984 / 1000) ^ 162 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 162 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 162 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 162 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 162 : ℚ) ^ 2 / 162) <
      311 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 162 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_163 :
    barrierV2 163 ^ 2 / 163 < (3509 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 163 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 163 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 163 +
      (4451662 / 100000000) * (-96 / 100) ^ 163 +
      (2545398 / 100000000) * (88 / 100) ^ 163 +
      (-4932634 / 100000000) * (95 / 100) ^ 163 +
      (11618157 / 100000000) * (984 / 1000) ^ 163 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 163 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 163 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 163 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 163 : ℚ) ^ 2 / 163) <
      3509 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 163 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_164 :
    barrierV2 164 ^ 2 / 164 < (576 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 164 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 164 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 164 +
      (4451662 / 100000000) * (-96 / 100) ^ 164 +
      (2545398 / 100000000) * (88 / 100) ^ 164 +
      (-4932634 / 100000000) * (95 / 100) ^ 164 +
      (11618157 / 100000000) * (984 / 1000) ^ 164 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 164 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 164 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 164 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 164 : ℚ) ^ 2 / 164) <
      576 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 164 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_165 :
    barrierV2 165 ^ 2 / 165 < (302 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 165 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 165 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 165 +
      (4451662 / 100000000) * (-96 / 100) ^ 165 +
      (2545398 / 100000000) * (88 / 100) ^ 165 +
      (-4932634 / 100000000) * (95 / 100) ^ 165 +
      (11618157 / 100000000) * (984 / 1000) ^ 165 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 165 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 165 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 165 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 165 : ℚ) ^ 2 / 165) <
      302 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 165 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_166 :
    barrierV2 166 ^ 2 / 166 < (267 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 166 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 166 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 166 +
      (4451662 / 100000000) * (-96 / 100) ^ 166 +
      (2545398 / 100000000) * (88 / 100) ^ 166 +
      (-4932634 / 100000000) * (95 / 100) ^ 166 +
      (11618157 / 100000000) * (984 / 1000) ^ 166 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 166 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 166 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 166 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 166 : ℚ) ^ 2 / 166) <
      267 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 166 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_167 :
    barrierV2 167 ^ 2 / 167 < (3014 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 167 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 167 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 167 +
      (4451662 / 100000000) * (-96 / 100) ^ 167 +
      (2545398 / 100000000) * (88 / 100) ^ 167 +
      (-4932634 / 100000000) * (95 / 100) ^ 167 +
      (11618157 / 100000000) * (984 / 1000) ^ 167 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 167 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 167 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 167 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 167 : ℚ) ^ 2 / 167) <
      3014 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 167 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_168 :
    barrierV2 168 ^ 2 / 168 < (494 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 168 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 168 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 168 +
      (4451662 / 100000000) * (-96 / 100) ^ 168 +
      (2545398 / 100000000) * (88 / 100) ^ 168 +
      (-4932634 / 100000000) * (95 / 100) ^ 168 +
      (11618157 / 100000000) * (984 / 1000) ^ 168 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 168 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 168 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 168 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 168 : ℚ) ^ 2 / 168) <
      494 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 168 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_168 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (160 + k + 1) ^ 2 / ((160 + k + 1 : ℕ) : ℝ)) ≤
      (8825 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_161.le) barrierV2_norm_term_162.le) barrierV2_norm_term_163.le) barrierV2_norm_term_164.le) barrierV2_norm_term_165.le) barrierV2_norm_term_166.le) barrierV2_norm_term_167.le) barrierV2_norm_term_168.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_168 :
    (∑ k ∈ Finset.range 168,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291623128 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (160 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_160 barrierV2_norm_block_168
  have hc : (1291614303 / 1000000000 : ℝ) + 8825 / 1000000000 =
      1291623128 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_169 :
    barrierV2 169 ^ 2 / 169 < (260 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 169 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 169 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 169 +
      (4451662 / 100000000) * (-96 / 100) ^ 169 +
      (2545398 / 100000000) * (88 / 100) ^ 169 +
      (-4932634 / 100000000) * (95 / 100) ^ 169 +
      (11618157 / 100000000) * (984 / 1000) ^ 169 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 169 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 169 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 169 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 169 : ℚ) ^ 2 / 169) <
      260 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 169 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_170 :
    barrierV2 170 ^ 2 / 170 < (228 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 170 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 170 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 170 +
      (4451662 / 100000000) * (-96 / 100) ^ 170 +
      (2545398 / 100000000) * (88 / 100) ^ 170 +
      (-4932634 / 100000000) * (95 / 100) ^ 170 +
      (11618157 / 100000000) * (984 / 1000) ^ 170 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 170 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 170 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 170 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 170 : ℚ) ^ 2 / 170) <
      228 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 170 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_171 :
    barrierV2 171 ^ 2 / 171 < (2590 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 171 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 171 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 171 +
      (4451662 / 100000000) * (-96 / 100) ^ 171 +
      (2545398 / 100000000) * (88 / 100) ^ 171 +
      (-4932634 / 100000000) * (95 / 100) ^ 171 +
      (11618157 / 100000000) * (984 / 1000) ^ 171 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 171 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 171 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 171 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 171 : ℚ) ^ 2 / 171) <
      2590 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 171 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_172 :
    barrierV2 172 ^ 2 / 172 < (424 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 172 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 172 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 172 +
      (4451662 / 100000000) * (-96 / 100) ^ 172 +
      (2545398 / 100000000) * (88 / 100) ^ 172 +
      (-4932634 / 100000000) * (95 / 100) ^ 172 +
      (11618157 / 100000000) * (984 / 1000) ^ 172 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 172 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 172 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 172 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 172 : ℚ) ^ 2 / 172) <
      424 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 172 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_173 :
    barrierV2 173 ^ 2 / 173 < (223 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 173 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 173 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 173 +
      (4451662 / 100000000) * (-96 / 100) ^ 173 +
      (2545398 / 100000000) * (88 / 100) ^ 173 +
      (-4932634 / 100000000) * (95 / 100) ^ 173 +
      (11618157 / 100000000) * (984 / 1000) ^ 173 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 173 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 173 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 173 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 173 : ℚ) ^ 2 / 173) <
      223 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 173 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_174 :
    barrierV2 174 ^ 2 / 174 < (196 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 174 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 174 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 174 +
      (4451662 / 100000000) * (-96 / 100) ^ 174 +
      (2545398 / 100000000) * (88 / 100) ^ 174 +
      (-4932634 / 100000000) * (95 / 100) ^ 174 +
      (11618157 / 100000000) * (984 / 1000) ^ 174 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 174 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 174 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 174 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 174 : ℚ) ^ 2 / 174) <
      196 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 174 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_175 :
    barrierV2 175 ^ 2 / 175 < (2227 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 175 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 175 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 175 +
      (4451662 / 100000000) * (-96 / 100) ^ 175 +
      (2545398 / 100000000) * (88 / 100) ^ 175 +
      (-4932634 / 100000000) * (95 / 100) ^ 175 +
      (11618157 / 100000000) * (984 / 1000) ^ 175 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 175 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 175 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 175 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 175 : ℚ) ^ 2 / 175) <
      2227 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 175 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_176 :
    barrierV2 176 ^ 2 / 176 < (365 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 176 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 176 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 176 +
      (4451662 / 100000000) * (-96 / 100) ^ 176 +
      (2545398 / 100000000) * (88 / 100) ^ 176 +
      (-4932634 / 100000000) * (95 / 100) ^ 176 +
      (11618157 / 100000000) * (984 / 1000) ^ 176 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 176 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 176 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 176 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 176 : ℚ) ^ 2 / 176) <
      365 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 176 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_176 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (168 + k + 1) ^ 2 / ((168 + k + 1 : ℕ) : ℝ)) ≤
      (6513 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_169.le) barrierV2_norm_term_170.le) barrierV2_norm_term_171.le) barrierV2_norm_term_172.le) barrierV2_norm_term_173.le) barrierV2_norm_term_174.le) barrierV2_norm_term_175.le) barrierV2_norm_term_176.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_176 :
    (∑ k ∈ Finset.range 176,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291629641 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (168 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_168 barrierV2_norm_block_176
  have hc : (1291623128 / 1000000000 : ℝ) + 6513 / 1000000000 =
      1291629641 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_177 :
    barrierV2 177 ^ 2 / 177 < (192 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 177 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 177 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 177 +
      (4451662 / 100000000) * (-96 / 100) ^ 177 +
      (2545398 / 100000000) * (88 / 100) ^ 177 +
      (-4932634 / 100000000) * (95 / 100) ^ 177 +
      (11618157 / 100000000) * (984 / 1000) ^ 177 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 177 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 177 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 177 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 177 : ℚ) ^ 2 / 177) <
      192 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 177 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_178 :
    barrierV2 178 ^ 2 / 178 < (168 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 178 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 178 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 178 +
      (4451662 / 100000000) * (-96 / 100) ^ 178 +
      (2545398 / 100000000) * (88 / 100) ^ 178 +
      (-4932634 / 100000000) * (95 / 100) ^ 178 +
      (11618157 / 100000000) * (984 / 1000) ^ 178 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 178 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 178 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 178 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 178 : ℚ) ^ 2 / 178) <
      168 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 178 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_179 :
    barrierV2 179 ^ 2 / 179 < (1915 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 179 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 179 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 179 +
      (4451662 / 100000000) * (-96 / 100) ^ 179 +
      (2545398 / 100000000) * (88 / 100) ^ 179 +
      (-4932634 / 100000000) * (95 / 100) ^ 179 +
      (11618157 / 100000000) * (984 / 1000) ^ 179 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 179 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 179 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 179 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 179 : ℚ) ^ 2 / 179) <
      1915 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 179 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_180 :
    barrierV2 180 ^ 2 / 180 < (313 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 180 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 180 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 180 +
      (4451662 / 100000000) * (-96 / 100) ^ 180 +
      (2545398 / 100000000) * (88 / 100) ^ 180 +
      (-4932634 / 100000000) * (95 / 100) ^ 180 +
      (11618157 / 100000000) * (984 / 1000) ^ 180 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 180 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 180 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 180 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 180 : ℚ) ^ 2 / 180) <
      313 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 180 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_181 :
    barrierV2 181 ^ 2 / 181 < (165 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 181 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 181 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 181 +
      (4451662 / 100000000) * (-96 / 100) ^ 181 +
      (2545398 / 100000000) * (88 / 100) ^ 181 +
      (-4932634 / 100000000) * (95 / 100) ^ 181 +
      (11618157 / 100000000) * (984 / 1000) ^ 181 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 181 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 181 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 181 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 181 : ℚ) ^ 2 / 181) <
      165 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 181 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_182 :
    barrierV2 182 ^ 2 / 182 < (144 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 182 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 182 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 182 +
      (4451662 / 100000000) * (-96 / 100) ^ 182 +
      (2545398 / 100000000) * (88 / 100) ^ 182 +
      (-4932634 / 100000000) * (95 / 100) ^ 182 +
      (11618157 / 100000000) * (984 / 1000) ^ 182 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 182 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 182 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 182 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 182 : ℚ) ^ 2 / 182) <
      144 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 182 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_183 :
    barrierV2 183 ^ 2 / 183 < (1648 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 183 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 183 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 183 +
      (4451662 / 100000000) * (-96 / 100) ^ 183 +
      (2545398 / 100000000) * (88 / 100) ^ 183 +
      (-4932634 / 100000000) * (95 / 100) ^ 183 +
      (11618157 / 100000000) * (984 / 1000) ^ 183 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 183 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 183 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 183 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 183 : ℚ) ^ 2 / 183) <
      1648 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 183 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_184 :
    barrierV2 184 ^ 2 / 184 < (270 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 184 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 184 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 184 +
      (4451662 / 100000000) * (-96 / 100) ^ 184 +
      (2545398 / 100000000) * (88 / 100) ^ 184 +
      (-4932634 / 100000000) * (95 / 100) ^ 184 +
      (11618157 / 100000000) * (984 / 1000) ^ 184 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 184 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 184 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 184 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 184 : ℚ) ^ 2 / 184) <
      270 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 184 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_184 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (176 + k + 1) ^ 2 / ((176 + k + 1 : ℕ) : ℝ)) ≤
      (4815 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_177.le) barrierV2_norm_term_178.le) barrierV2_norm_term_179.le) barrierV2_norm_term_180.le) barrierV2_norm_term_181.le) barrierV2_norm_term_182.le) barrierV2_norm_term_183.le) barrierV2_norm_term_184.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_184 :
    (∑ k ∈ Finset.range 184,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291634456 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (176 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_176 barrierV2_norm_block_184
  have hc : (1291629641 / 1000000000 : ℝ) + 4815 / 1000000000 =
      1291634456 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_185 :
    barrierV2 185 ^ 2 / 185 < (142 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 185 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 185 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 185 +
      (4451662 / 100000000) * (-96 / 100) ^ 185 +
      (2545398 / 100000000) * (88 / 100) ^ 185 +
      (-4932634 / 100000000) * (95 / 100) ^ 185 +
      (11618157 / 100000000) * (984 / 1000) ^ 185 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 185 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 185 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 185 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 185 : ℚ) ^ 2 / 185) <
      142 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 185 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_186 :
    barrierV2 186 ^ 2 / 186 < (124 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 186 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 186 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 186 +
      (4451662 / 100000000) * (-96 / 100) ^ 186 +
      (2545398 / 100000000) * (88 / 100) ^ 186 +
      (-4932634 / 100000000) * (95 / 100) ^ 186 +
      (11618157 / 100000000) * (984 / 1000) ^ 186 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 186 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 186 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 186 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 186 : ℚ) ^ 2 / 186) <
      124 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 186 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_187 :
    barrierV2 187 ^ 2 / 187 < (1418 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 187 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 187 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 187 +
      (4451662 / 100000000) * (-96 / 100) ^ 187 +
      (2545398 / 100000000) * (88 / 100) ^ 187 +
      (-4932634 / 100000000) * (95 / 100) ^ 187 +
      (11618157 / 100000000) * (984 / 1000) ^ 187 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 187 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 187 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 187 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 187 : ℚ) ^ 2 / 187) <
      1418 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 187 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_188 :
    barrierV2 188 ^ 2 / 188 < (232 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 188 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 188 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 188 +
      (4451662 / 100000000) * (-96 / 100) ^ 188 +
      (2545398 / 100000000) * (88 / 100) ^ 188 +
      (-4932634 / 100000000) * (95 / 100) ^ 188 +
      (11618157 / 100000000) * (984 / 1000) ^ 188 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 188 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 188 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 188 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 188 : ℚ) ^ 2 / 188) <
      232 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 188 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_189 :
    barrierV2 189 ^ 2 / 189 < (122 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 189 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 189 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 189 +
      (4451662 / 100000000) * (-96 / 100) ^ 189 +
      (2545398 / 100000000) * (88 / 100) ^ 189 +
      (-4932634 / 100000000) * (95 / 100) ^ 189 +
      (11618157 / 100000000) * (984 / 1000) ^ 189 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 189 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 189 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 189 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 189 : ℚ) ^ 2 / 189) <
      122 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 189 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_190 :
    barrierV2 190 ^ 2 / 190 < (107 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 190 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 190 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 190 +
      (4451662 / 100000000) * (-96 / 100) ^ 190 +
      (2545398 / 100000000) * (88 / 100) ^ 190 +
      (-4932634 / 100000000) * (95 / 100) ^ 190 +
      (11618157 / 100000000) * (984 / 1000) ^ 190 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 190 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 190 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 190 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 190 : ℚ) ^ 2 / 190) <
      107 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 190 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_191 :
    barrierV2 191 ^ 2 / 191 < (1221 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 191 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 191 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 191 +
      (4451662 / 100000000) * (-96 / 100) ^ 191 +
      (2545398 / 100000000) * (88 / 100) ^ 191 +
      (-4932634 / 100000000) * (95 / 100) ^ 191 +
      (11618157 / 100000000) * (984 / 1000) ^ 191 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 191 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 191 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 191 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 191 : ℚ) ^ 2 / 191) <
      1221 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 191 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_192 :
    barrierV2 192 ^ 2 / 192 < (200 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 192 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 192 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 192 +
      (4451662 / 100000000) * (-96 / 100) ^ 192 +
      (2545398 / 100000000) * (88 / 100) ^ 192 +
      (-4932634 / 100000000) * (95 / 100) ^ 192 +
      (11618157 / 100000000) * (984 / 1000) ^ 192 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 192 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 192 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 192 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 192 : ℚ) ^ 2 / 192) <
      200 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 192 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_192 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (184 + k + 1) ^ 2 / ((184 + k + 1 : ℕ) : ℝ)) ≤
      (3566 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_185.le) barrierV2_norm_term_186.le) barrierV2_norm_term_187.le) barrierV2_norm_term_188.le) barrierV2_norm_term_189.le) barrierV2_norm_term_190.le) barrierV2_norm_term_191.le) barrierV2_norm_term_192.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_192 :
    (∑ k ∈ Finset.range 192,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291638022 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (184 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_184 barrierV2_norm_block_192
  have hc : (1291634456 / 1000000000 : ℝ) + 3566 / 1000000000 =
      1291638022 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end

end OAI
