import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import OAI.NumberTheory.Catalan.Energy.BarrierTwoNormVPrefix192

namespace OAI


noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_193 :
    barrierV2 193 ^ 2 / 193 < (105 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 193 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 193 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 193 +
      (4451662 / 100000000) * (-96 / 100) ^ 193 +
      (2545398 / 100000000) * (88 / 100) ^ 193 +
      (-4932634 / 100000000) * (95 / 100) ^ 193 +
      (11618157 / 100000000) * (984 / 1000) ^ 193 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 193 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 193 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 193 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 193 : ℚ) ^ 2 / 193) <
      105 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 193 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_194 :
    barrierV2 194 ^ 2 / 194 < (92 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 194 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 194 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 194 +
      (4451662 / 100000000) * (-96 / 100) ^ 194 +
      (2545398 / 100000000) * (88 / 100) ^ 194 +
      (-4932634 / 100000000) * (95 / 100) ^ 194 +
      (11618157 / 100000000) * (984 / 1000) ^ 194 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 194 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 194 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 194 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 194 : ℚ) ^ 2 / 194) <
      92 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 194 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero,
    mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_195 :
    barrierV2 195 ^ 2 / 195 < (1052 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 195 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 195 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 195 +
      (4451662 / 100000000) * (-96 / 100) ^ 195 +
      (2545398 / 100000000) * (88 / 100) ^ 195 +
      (-4932634 / 100000000) * (95 / 100) ^ 195 +
      (11618157 / 100000000) * (984 / 1000) ^ 195 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 195 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 195 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 195 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 195 : ℚ) ^ 2 / 195) <
      1052 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 195 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg,
    mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_196 :
    barrierV2 196 ^ 2 / 196 < (172 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 196 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 196 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 196 +
      (4451662 / 100000000) * (-96 / 100) ^ 196 +
      (2545398 / 100000000) * (88 / 100) ^ 196 +
      (-4932634 / 100000000) * (95 / 100) ^ 196 +
      (11618157 / 100000000) * (984 / 1000) ^ 196 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 196 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 196 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 196 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 196 : ℚ) ^ 2 / 196) <
      172 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 196 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_197 :
    barrierV2 197 ^ 2 / 197 < (91 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 197 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 197 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 197 +
      (4451662 / 100000000) * (-96 / 100) ^ 197 +
      (2545398 / 100000000) * (88 / 100) ^ 197 +
      (-4932634 / 100000000) * (95 / 100) ^ 197 +
      (11618157 / 100000000) * (984 / 1000) ^ 197 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 197 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 197 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 197 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 197 : ℚ) ^ 2 / 197) <
      91 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 197 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_198 :
    barrierV2 198 ^ 2 / 198 < (79 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 198 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 198 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 198 +
      (4451662 / 100000000) * (-96 / 100) ^ 198 +
      (2545398 / 100000000) * (88 / 100) ^ 198 +
      (-4932634 / 100000000) * (95 / 100) ^ 198 +
      (11618157 / 100000000) * (984 / 1000) ^ 198 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 198 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 198 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 198 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 198 : ℚ) ^ 2 / 198) <
      79 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 198 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero,
    mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_199 :
    barrierV2 199 ^ 2 / 199 < (907 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 199 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 199 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 199 +
      (4451662 / 100000000) * (-96 / 100) ^ 199 +
      (2545398 / 100000000) * (88 / 100) ^ 199 +
      (-4932634 / 100000000) * (95 / 100) ^ 199 +
      (11618157 / 100000000) * (984 / 1000) ^ 199 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 199 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 199 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 199 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 199 : ℚ) ^ 2 / 199) <
      907 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 199 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg,
    mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_200 :
    barrierV2 200 ^ 2 / 200 < (148 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 200 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 200 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 200 +
      (4451662 / 100000000) * (-96 / 100) ^ 200 +
      (2545398 / 100000000) * (88 / 100) ^ 200 +
      (-4932634 / 100000000) * (95 / 100) ^ 200 +
      (11618157 / 100000000) * (984 / 1000) ^ 200 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 200 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 200 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 200 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 200 : ℚ) ^ 2 / 200) <
      148 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 200 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_200 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (192 + k + 1) ^ 2 / ((192 + k + 1 : ℕ) : ℝ)) ≤
      (2646 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_193.le) barrierV2_norm_term_194.le) barrierV2_norm_term_195.le) barrierV2_norm_term_196.le) barrierV2_norm_term_197.le) barrierV2_norm_term_198.le) barrierV2_norm_term_199.le) barrierV2_norm_term_200.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_200 :
    (∑ k ∈ Finset.range 200,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291640668 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (192 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_192 barrierV2_norm_block_200
  have hc : (1291638022 / 1000000000 : ℝ) + 2646 / 1000000000 =
      1291640668 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_201 :
    barrierV2 201 ^ 2 / 201 < (78 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 201 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 201 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 201 +
      (4451662 / 100000000) * (-96 / 100) ^ 201 +
      (2545398 / 100000000) * (88 / 100) ^ 201 +
      (-4932634 / 100000000) * (95 / 100) ^ 201 +
      (11618157 / 100000000) * (984 / 1000) ^ 201 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 201 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 201 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 201 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 201 : ℚ) ^ 2 / 201) <
      78 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 201 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_202 :
    barrierV2 202 ^ 2 / 202 < (68 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 202 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 202 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 202 +
      (4451662 / 100000000) * (-96 / 100) ^ 202 +
      (2545398 / 100000000) * (88 / 100) ^ 202 +
      (-4932634 / 100000000) * (95 / 100) ^ 202 +
      (11618157 / 100000000) * (984 / 1000) ^ 202 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 202 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 202 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 202 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 202 : ℚ) ^ 2 / 202) <
      68 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 202 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero,
    mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_203 :
    barrierV2 203 ^ 2 / 203 < (782 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 203 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 203 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 203 +
      (4451662 / 100000000) * (-96 / 100) ^ 203 +
      (2545398 / 100000000) * (88 / 100) ^ 203 +
      (-4932634 / 100000000) * (95 / 100) ^ 203 +
      (11618157 / 100000000) * (984 / 1000) ^ 203 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 203 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 203 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 203 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 203 : ℚ) ^ 2 / 203) <
      782 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 203 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg,
    mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_204 :
    barrierV2 204 ^ 2 / 204 < (128 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 204 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 204 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 204 +
      (4451662 / 100000000) * (-96 / 100) ^ 204 +
      (2545398 / 100000000) * (88 / 100) ^ 204 +
      (-4932634 / 100000000) * (95 / 100) ^ 204 +
      (11618157 / 100000000) * (984 / 1000) ^ 204 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 204 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 204 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 204 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 204 : ℚ) ^ 2 / 204) <
      128 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 204 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_205 :
    barrierV2 205 ^ 2 / 205 < (67 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 205 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 205 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 205 +
      (4451662 / 100000000) * (-96 / 100) ^ 205 +
      (2545398 / 100000000) * (88 / 100) ^ 205 +
      (-4932634 / 100000000) * (95 / 100) ^ 205 +
      (11618157 / 100000000) * (984 / 1000) ^ 205 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 205 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 205 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 205 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 205 : ℚ) ^ 2 / 205) <
      67 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 205 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_206 :
    barrierV2 206 ^ 2 / 206 < (59 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 206 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 206 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 206 +
      (4451662 / 100000000) * (-96 / 100) ^ 206 +
      (2545398 / 100000000) * (88 / 100) ^ 206 +
      (-4932634 / 100000000) * (95 / 100) ^ 206 +
      (11618157 / 100000000) * (984 / 1000) ^ 206 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 206 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 206 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 206 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 206 : ℚ) ^ 2 / 206) <
      59 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 206 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero,
    mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_207 :
    barrierV2 207 ^ 2 / 207 < (674 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 207 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 207 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 207 +
      (4451662 / 100000000) * (-96 / 100) ^ 207 +
      (2545398 / 100000000) * (88 / 100) ^ 207 +
      (-4932634 / 100000000) * (95 / 100) ^ 207 +
      (11618157 / 100000000) * (984 / 1000) ^ 207 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 207 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 207 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 207 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 207 : ℚ) ^ 2 / 207) <
      674 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 207 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg,
    mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_208 :
    barrierV2 208 ^ 2 / 208 < (110 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 208 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 208 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 208 +
      (4451662 / 100000000) * (-96 / 100) ^ 208 +
      (2545398 / 100000000) * (88 / 100) ^ 208 +
      (-4932634 / 100000000) * (95 / 100) ^ 208 +
      (11618157 / 100000000) * (984 / 1000) ^ 208 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 208 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 208 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 208 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 208 : ℚ) ^ 2 / 208) <
      110 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 208 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_208 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (200 + k + 1) ^ 2 / ((200 + k + 1 : ℕ) : ℝ)) ≤
      (1966 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_201.le) barrierV2_norm_term_202.le) barrierV2_norm_term_203.le) barrierV2_norm_term_204.le) barrierV2_norm_term_205.le) barrierV2_norm_term_206.le) barrierV2_norm_term_207.le) barrierV2_norm_term_208.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_208 :
    (∑ k ∈ Finset.range 208,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291642634 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (200 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_200 barrierV2_norm_block_208
  have hc : (1291640668 / 1000000000 : ℝ) + 1966 / 1000000000 =
      1291642634 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_209 :
    barrierV2 209 ^ 2 / 209 < (58 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 209 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 209 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 209 +
      (4451662 / 100000000) * (-96 / 100) ^ 209 +
      (2545398 / 100000000) * (88 / 100) ^ 209 +
      (-4932634 / 100000000) * (95 / 100) ^ 209 +
      (11618157 / 100000000) * (984 / 1000) ^ 209 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 209 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 209 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 209 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 209 : ℚ) ^ 2 / 209) <
      58 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 209 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_210 :
    barrierV2 210 ^ 2 / 210 < (51 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 210 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 210 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 210 +
      (4451662 / 100000000) * (-96 / 100) ^ 210 +
      (2545398 / 100000000) * (88 / 100) ^ 210 +
      (-4932634 / 100000000) * (95 / 100) ^ 210 +
      (11618157 / 100000000) * (984 / 1000) ^ 210 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 210 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 210 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 210 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 210 : ℚ) ^ 2 / 210) <
      51 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 210 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero,
    mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_211 :
    barrierV2 211 ^ 2 / 211 < (581 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 211 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 211 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 211 +
      (4451662 / 100000000) * (-96 / 100) ^ 211 +
      (2545398 / 100000000) * (88 / 100) ^ 211 +
      (-4932634 / 100000000) * (95 / 100) ^ 211 +
      (11618157 / 100000000) * (984 / 1000) ^ 211 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 211 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 211 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 211 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 211 : ℚ) ^ 2 / 211) <
      581 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 211 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg,
    mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_212 :
    barrierV2 212 ^ 2 / 212 < (95 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 212 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 212 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 212 +
      (4451662 / 100000000) * (-96 / 100) ^ 212 +
      (2545398 / 100000000) * (88 / 100) ^ 212 +
      (-4932634 / 100000000) * (95 / 100) ^ 212 +
      (11618157 / 100000000) * (984 / 1000) ^ 212 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 212 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 212 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 212 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 212 : ℚ) ^ 2 / 212) <
      95 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 212 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_213 :
    barrierV2 213 ^ 2 / 213 < (50 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 213 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 213 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 213 +
      (4451662 / 100000000) * (-96 / 100) ^ 213 +
      (2545398 / 100000000) * (88 / 100) ^ 213 +
      (-4932634 / 100000000) * (95 / 100) ^ 213 +
      (11618157 / 100000000) * (984 / 1000) ^ 213 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 213 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 213 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 213 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 213 : ℚ) ^ 2 / 213) <
      50 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 213 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_214 :
    barrierV2 214 ^ 2 / 214 < (44 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 214 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 214 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 214 +
      (4451662 / 100000000) * (-96 / 100) ^ 214 +
      (2545398 / 100000000) * (88 / 100) ^ 214 +
      (-4932634 / 100000000) * (95 / 100) ^ 214 +
      (11618157 / 100000000) * (984 / 1000) ^ 214 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 214 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 214 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 214 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 214 : ℚ) ^ 2 / 214) <
      44 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 214 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero,
    mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_215 :
    barrierV2 215 ^ 2 / 215 < (502 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 215 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 215 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 215 +
      (4451662 / 100000000) * (-96 / 100) ^ 215 +
      (2545398 / 100000000) * (88 / 100) ^ 215 +
      (-4932634 / 100000000) * (95 / 100) ^ 215 +
      (11618157 / 100000000) * (984 / 1000) ^ 215 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 215 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 215 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 215 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 215 : ℚ) ^ 2 / 215) <
      502 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 215 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg,
    mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_216 :
    barrierV2 216 ^ 2 / 216 < (82 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 216 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 216 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 216 +
      (4451662 / 100000000) * (-96 / 100) ^ 216 +
      (2545398 / 100000000) * (88 / 100) ^ 216 +
      (-4932634 / 100000000) * (95 / 100) ^ 216 +
      (11618157 / 100000000) * (984 / 1000) ^ 216 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 216 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 216 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 216 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 216 : ℚ) ^ 2 / 216) <
      82 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 216 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_216 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (208 + k + 1) ^ 2 / ((208 + k + 1 : ℕ) : ℝ)) ≤
      (1463 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_209.le) barrierV2_norm_term_210.le) barrierV2_norm_term_211.le) barrierV2_norm_term_212.le) barrierV2_norm_term_213.le) barrierV2_norm_term_214.le) barrierV2_norm_term_215.le) barrierV2_norm_term_216.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_216 :
    (∑ k ∈ Finset.range 216,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291644097 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (208 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_208 barrierV2_norm_block_216
  have hc : (1291642634 / 1000000000 : ℝ) + 1463 / 1000000000 =
      1291644097 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_217 :
    barrierV2 217 ^ 2 / 217 < (43 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 217 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 217 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 217 +
      (4451662 / 100000000) * (-96 / 100) ^ 217 +
      (2545398 / 100000000) * (88 / 100) ^ 217 +
      (-4932634 / 100000000) * (95 / 100) ^ 217 +
      (11618157 / 100000000) * (984 / 1000) ^ 217 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 217 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 217 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 217 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 217 : ℚ) ^ 2 / 217) <
      43 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 217 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_218 :
    barrierV2 218 ^ 2 / 218 < (38 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 218 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 218 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 218 +
      (4451662 / 100000000) * (-96 / 100) ^ 218 +
      (2545398 / 100000000) * (88 / 100) ^ 218 +
      (-4932634 / 100000000) * (95 / 100) ^ 218 +
      (11618157 / 100000000) * (984 / 1000) ^ 218 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 218 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 218 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 218 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 218 : ℚ) ^ 2 / 218) <
      38 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 218 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero,
    mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_219 :
    barrierV2 219 ^ 2 / 219 < (433 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 219 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 219 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 219 +
      (4451662 / 100000000) * (-96 / 100) ^ 219 +
      (2545398 / 100000000) * (88 / 100) ^ 219 +
      (-4932634 / 100000000) * (95 / 100) ^ 219 +
      (11618157 / 100000000) * (984 / 1000) ^ 219 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 219 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 219 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 219 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 219 : ℚ) ^ 2 / 219) <
      433 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 219 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg,
    mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_220 :
    barrierV2 220 ^ 2 / 220 < (71 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 220 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 220 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 220 +
      (4451662 / 100000000) * (-96 / 100) ^ 220 +
      (2545398 / 100000000) * (88 / 100) ^ 220 +
      (-4932634 / 100000000) * (95 / 100) ^ 220 +
      (11618157 / 100000000) * (984 / 1000) ^ 220 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 220 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 220 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 220 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 220 : ℚ) ^ 2 / 220) <
      71 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 220 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_221 :
    barrierV2 221 ^ 2 / 221 < (38 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 221 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 221 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 221 +
      (4451662 / 100000000) * (-96 / 100) ^ 221 +
      (2545398 / 100000000) * (88 / 100) ^ 221 +
      (-4932634 / 100000000) * (95 / 100) ^ 221 +
      (11618157 / 100000000) * (984 / 1000) ^ 221 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 221 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 221 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 221 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 221 : ℚ) ^ 2 / 221) <
      38 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 221 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_222 :
    barrierV2 222 ^ 2 / 222 < (33 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 222 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 222 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 222 +
      (4451662 / 100000000) * (-96 / 100) ^ 222 +
      (2545398 / 100000000) * (88 / 100) ^ 222 +
      (-4932634 / 100000000) * (95 / 100) ^ 222 +
      (11618157 / 100000000) * (984 / 1000) ^ 222 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 222 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 222 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 222 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 222 : ℚ) ^ 2 / 222) <
      33 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 222 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero,
    mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_223 :
    barrierV2 223 ^ 2 / 223 < (374 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 223 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 223 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 223 +
      (4451662 / 100000000) * (-96 / 100) ^ 223 +
      (2545398 / 100000000) * (88 / 100) ^ 223 +
      (-4932634 / 100000000) * (95 / 100) ^ 223 +
      (11618157 / 100000000) * (984 / 1000) ^ 223 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 223 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 223 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 223 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 223 : ℚ) ^ 2 / 223) <
      374 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 223 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg,
    mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_224 :
    barrierV2 224 ^ 2 / 224 < (61 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 224 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 224 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 224 +
      (4451662 / 100000000) * (-96 / 100) ^ 224 +
      (2545398 / 100000000) * (88 / 100) ^ 224 +
      (-4932634 / 100000000) * (95 / 100) ^ 224 +
      (11618157 / 100000000) * (984 / 1000) ^ 224 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 224 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 224 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 224 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 224 : ℚ) ^ 2 / 224) <
      61 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 224 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_224 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (216 + k + 1) ^ 2 / ((216 + k + 1 : ℕ) : ℝ)) ≤
      (1091 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_217.le) barrierV2_norm_term_218.le) barrierV2_norm_term_219.le) barrierV2_norm_term_220.le) barrierV2_norm_term_221.le) barrierV2_norm_term_222.le) barrierV2_norm_term_223.le) barrierV2_norm_term_224.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_224 :
    (∑ k ∈ Finset.range 224,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291645188 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (216 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_216 barrierV2_norm_block_224
  have hc : (1291644097 / 1000000000 : ℝ) + 1091 / 1000000000 =
      1291645188 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_225 :
    barrierV2 225 ^ 2 / 225 < (32 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 225 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 225 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 225 +
      (4451662 / 100000000) * (-96 / 100) ^ 225 +
      (2545398 / 100000000) * (88 / 100) ^ 225 +
      (-4932634 / 100000000) * (95 / 100) ^ 225 +
      (11618157 / 100000000) * (984 / 1000) ^ 225 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 225 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 225 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 225 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 225 : ℚ) ^ 2 / 225) <
      32 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 225 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_225 :
    (∑ k ∈ Finset.range 1,
      barrierV2 (224 + k + 1) ^ 2 / ((224 + k + 1 : ℕ) : ℝ)) ≤
      (32 / 1000000000 : ℝ) := by
  have h := (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_225.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_225 :
    (∑ k ∈ Finset.range 225,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291645220 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (224 + 1),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_224 barrierV2_norm_block_225
  have hc : (1291645188 / 1000000000 : ℝ) + 32 / 1000000000 =
      1291645220 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end

end OAI
