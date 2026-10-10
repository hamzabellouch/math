import OAI.NumberTheory.Ostmann.ZeroDensity.RealCharacterComplexification
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroInverseSquare

namespace OAI

/-! # Absolute convergence of the real-axis zero kernel -/

namespace Ostmann

theorem real_zero_kernel_square_bound (a y δ : ℝ) (hδ : 0 < δ)
    (ha : δ ≤ a) (ha2 : a ≤ 2) :
    realZeroKernel a y ≤ (8 + 4 * δ⁻¹) * ((1 + |y|) ^ 2)⁻¹ := by
  have ha0 : 0 < a := hδ.trans_le ha
  have hw : 0 < (1 + |y|) ^ 2 := sq_pos_of_pos (by positivity)
  by_cases hy : |y| ≤ 1
  · have hk := (realZeroKernel_le_inv (y := y) ha0).trans (inv_anti₀ hδ ha)
    have hwle : (1 + |y|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg y]
    have hwi : (1 / 4 : ℝ) ≤ ((1 + |y|) ^ 2)⁻¹ := by
      simpa using (inv_anti₀ hw hwle)
    have hm := mul_le_mul_of_nonneg_left hwi (by positivity : 0 ≤ 4 * δ⁻¹)
    have hn := mul_le_mul_of_nonneg_right (show 4 * δ⁻¹ ≤ 8 + 4 * δ⁻¹ by linarith)
      (inv_nonneg.mpr hw.le)
    nlinarith
  · have hy1 : 1 < |y| := lt_of_not_ge hy
    have hy2 : 0 < y ^ 2 := by nlinarith [sq_abs y]
    have hden : 0 < a ^ 2 + y ^ 2 := by positivity
    have hk : realZeroKernel a y ≤ 2 / y ^ 2 := by
      unfold realZeroKernel
      apply div_le_div₀ (by norm_num : (0 : ℝ) ≤ 2) ha2 hy2
      nlinarith [sq_nonneg a]
    have hwle : (1 + |y|) ^ 2 ≤ 4 * y ^ 2 := by nlinarith [sq_abs y]
    have hfrac : 2 / y ^ 2 ≤ 8 * ((1 + |y|) ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ hy2 hw]
      linarith
    exact (hk.trans hfrac).trans (mul_le_mul_of_nonneg_right (by have := inv_pos.mpr hδ; linarith)
      (inv_nonneg.mpr hw.le))

/-- The actual faithful zero family supplies the convergence field of the
published real-character Hadamard expansion. -/
theorem real_character_zero_kernel_summable (χ : PrimitiveRealCharacter) (s : ℝ)
    (hs : 1 < s) (hs2 : s ≤ 2) :
    Summable (fun i => realZeroKernel (s - ((realCharacterActualZeros χ).zeros i).re)
      ((realCharacterActualZeros χ).zeros i).im) := by
  let Z := realCharacterActualZeros χ
  have hh := character_zero_inverse_square_summable χ.asComplex
  apply Summable.of_nonneg_of_le
    (fun i => realZeroKernel_nonneg (by linarith [(Z.in_strip i).2]))
    (fun i => real_zero_kernel_square_bound _ _ (s - 1) (by linarith)
      (by linarith [(Z.in_strip i).2]) (by linarith [(Z.in_strip i).1]))
    (hh.mul_left (8 + 4 * (s - 1)⁻¹))

end Ostmann

end OAI
