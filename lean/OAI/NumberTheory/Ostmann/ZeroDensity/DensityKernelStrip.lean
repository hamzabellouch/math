import OAI.NumberTheory.Ostmann.ZeroDensity.DensitySmoothedKernel

namespace OAI

/-! # Uniform control of the square kernel between two positive vertical lines -/

namespace Ostmann

open Complex

 theorem densitySquareKernel_analytic (χ : PrimitiveComplexCharacter) (s w : ℂ)
    (hs : s.re = 1 / 2) (hw : 0 < w.re) :
    AnalyticAt ℂ (densitySquareKernel χ s) w := by
  have hq : (χ.modulus : ℂ) ≠ 0 := by exact_mod_cast χ.positive.ne'
  have hpos : 0 < (s + w).re := by simp only [add_re]; linarith
  have hΓ : AnalyticAt ℂ (DirichletCharacter.gammaFactor χ.character) (s + w) := by
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpos] with z hz
    exact χ.gammaFactor_differentiableAt_pos z hz
  have hd : AnalyticAt ℂ (fun z => DirichletCharacter.gammaFactor χ.character (s + z)) w :=
    hΓ.comp (analyticAt_const.add analyticAt_id)
  have hgn : DirichletCharacter.gammaFactor χ.character s ≠ 0 := by
    intro he
    exact χ.gammaInverse_ne_zero s (by linarith)
      (by simp only [PrimitiveComplexCharacter.gammaInverse, he, inv_zero])
  have hwn : w ≠ 0 := by intro h; simp [h] at hw
  exact ((((differentiable_id.const_cpow (Or.inl hq)).analyticAt w).mul
    ((hd.div analyticAt_const hgn).pow 2)).mul ((analyticAt_id.pow 2).cexp)).div analyticAt_id hwn

 theorem densitySquareKernel_strip_bound (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (c x u : ℝ) (hc : 0 < c) (hcx : c ≤ x) (hx : x ≤ 1) :
    ‖densitySquareKernel χ s ((x : ℂ) + u * I)‖ ≤
      (Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
        2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
        ((χ.modulus : ℝ) * (|s.im| + 2)) / c) * Real.exp (-(u ^ 2) / 2) := by
  let B := (χ.modulus : ℝ) * (|s.im| + 2)
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  have hB : 1 ≤ B := by dsimp [B]; nlinarith [abs_nonneg s.im]
  have hw0 : 0 ≤ (((x : ℂ) + u * I).re) := by simp; linarith
  have hw2 : (((x : ℂ) + u * I).re) ≤ 2 := by simp; linarith
  have hb := densityCompletedSquareWeight_bound χ s ((x : ℂ) + u * I) hs hw0 hw2
  have he : ((x : ℂ) + u * I).re = x := by simp
  have hi : ((x : ℂ) + u * I).im = u := by simp
  rw [he, hi] at hb
  have hp : B ^ x ≤ B :=
    (Real.rpow_le_rpow_of_exponent_le hB hx).trans_eq (Real.rpow_one B)
  have hcn : c ≤ ‖(x : ℂ) + u * I‖ := by
    exact hcx.trans (by simpa only [he] using Complex.re_le_norm ((x : ℂ) + u * I))
  rw [densitySquareKernel, norm_div]
  apply (div_le_div_of_nonneg_left (norm_nonneg _) hc hcn).trans
  apply (div_le_div_of_nonneg_right hb hc.le).trans
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp
    (Real.exp_nonneg (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
      2 * (59 + |Real.eulerMascheroniConstant|) ^ 2))) (Real.exp_nonneg (-(u ^ 2) / 2))
  have hd := div_le_div_of_nonneg_right h hc.le
  convert hd using 1
  ring

end Ostmann

end OAI
