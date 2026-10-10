import OAI.NumberTheory.Ostmann.ZeroDensity.SharpGammaRealShift
import OAI.NumberTheory.Ostmann.Characters.CharacterRootNumberUnit

namespace OAI

/-! # Uniform shifted Gamma factors for actual primitive characters -/

namespace Ostmann

open Complex
open scoped Classical

 theorem character_gamma_shift (χ : PrimitiveComplexCharacter) (s w : ℂ)
    (hs : s.re = 1 / 2) (hw : 0 ≤ w.re) (hw2 : w.re ≤ 2) :
    ‖DirichletCharacter.gammaFactor χ.character (s + w) /
        DirichletCharacter.gammaFactor χ.character s‖ ≤
      Real.exp ((59 + |Real.eulerMascheroniConstant|) * (1 + |w.im|)) *
        (|s.im| + 2) ^ (w.re / 2) := by
  by_cases he : χ.character.Even
  · simpa only [DirichletCharacter.gammaFactor, he, ↓reduceIte] using
      sharp_gammaReal_shift s w (by linarith) (by linarith) hw hw2
  · have h := sharp_gammaReal_shift (s + 1) w
      (by simp; linarith) (by simp; linarith) hw hw2
    simpa only [DirichletCharacter.gammaFactor, he, ↓reduceIte, add_im, one_im,
      add_zero, add_right_comm s w 1] using h

noncomputable def densityCompletedSquareWeight (χ : PrimitiveComplexCharacter) (s w : ℂ) : ℂ :=
  (χ.modulus : ℂ) ^ w *
    (DirichletCharacter.gammaFactor χ.character (s + w) /
      DirichletCharacter.gammaFactor χ.character s) ^ 2 * Complex.exp (w ^ 2)

 theorem gaussian_linear_abs_bound (C σ u : ℝ) (hσ : 0 ≤ σ) (hσ2 : σ ≤ 2) :
    Real.exp (2 * C * (1 + |u|) + σ ^ 2 - u ^ 2) ≤
      Real.exp (2 * C + 4 + 2 * C ^ 2) * Real.exp (-(u ^ 2) / 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (|u| - 2 * C), sq_abs u]

 theorem densityCompletedSquareWeight_bound (χ : PrimitiveComplexCharacter) (s w : ℂ)
    (hs : s.re = 1 / 2) (hw : 0 ≤ w.re) (hw2 : w.re ≤ 2) :
    ‖densityCompletedSquareWeight χ s w‖ ≤
      Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
        2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
      ((χ.modulus : ℝ) * (|s.im| + 2)) ^ w.re * Real.exp (-(w.im ^ 2) / 2) := by
  let C : ℝ := 59 + |Real.eulerMascheroniConstant|
  have hq : (0 : ℝ) < χ.modulus := by exact_mod_cast χ.positive
  have hG := character_gamma_shift χ s w hs hw hw2
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hG 2
  have hp : ‖(χ.modulus : ℂ) ^ w‖ = (χ.modulus : ℝ) ^ w.re := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq]
  have he : ‖Complex.exp (w ^ 2)‖ = Real.exp (w.re ^ 2 - w.im ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two, Complex.mul_re]
  have hsquare : (Real.exp (C * (1 + |w.im|)) * (|s.im| + 2) ^ (w.re / 2)) ^ 2 =
      Real.exp (2 * C * (1 + |w.im|)) * (|s.im| + 2) ^ w.re := by
    rw [mul_pow, ← Real.exp_nat_mul, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity : 0 ≤ |s.im| + 2)]
    congr 1
    · congr 1
      norm_num
      ring
    · congr 1
      norm_num
  have hpow : (χ.modulus : ℝ) ^ w.re * (|s.im| + 2) ^ w.re =
      ((χ.modulus : ℝ) * (|s.im| + 2)) ^ w.re :=
    (Real.mul_rpow hq.le (by positivity)).symm
  calc
    _ ≤ (χ.modulus : ℝ) ^ w.re *
        (Real.exp (C * (1 + |w.im|)) * (|s.im| + 2) ^ (w.re / 2)) ^ 2 *
        Real.exp (w.re ^ 2 - w.im ^ 2) := by
      simpa only [densityCompletedSquareWeight, norm_mul, norm_pow, hp, he] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity))
          (Real.exp_nonneg (w.re ^ 2 - w.im ^ 2))
    _ = ((χ.modulus : ℝ) * (|s.im| + 2)) ^ w.re *
        Real.exp (2 * C * (1 + |w.im|) + w.re ^ 2 - w.im ^ 2) := by
      rw [hsquare, show 2 * C * (1 + |w.im|) + w.re ^ 2 - w.im ^ 2 =
        2 * C * (1 + |w.im|) + (w.re ^ 2 - w.im ^ 2) by ring, Real.exp_add, ← hpow]
      ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (gaussian_linear_abs_bound C w.re w.im hw hw2)
        (Real.rpow_nonneg (mul_nonneg hq.le (by positivity : 0 ≤ |s.im| + 2)) w.re)
      simpa only [C, mul_assoc, mul_left_comm] using h

end Ostmann

end OAI
