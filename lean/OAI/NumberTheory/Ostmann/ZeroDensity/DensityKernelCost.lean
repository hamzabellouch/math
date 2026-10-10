import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFiniteSquareEnergy

namespace OAI

/-! # A common height and conductor cost for the smoothed square -/

namespace Ostmann

open Complex

noncomputable def densityKernelConstant : ℝ :=
  Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
    2 * (59 + |Real.eulerMascheroniConstant|) ^ 2)

noncomputable def densityKernelCost (Q : ℕ) (T c : ℝ) : ℝ :=
  densityKernelConstant * (10 * Q * T) ^ c / c

 theorem densityKernelConstant_pos : 0 < densityKernelConstant := Real.exp_pos _

 theorem densityKernelCost_pos (Q : ℕ) (hQ : 1 ≤ Q) (T c : ℝ)
    (hT : 1 ≤ T) (hc : 0 < c) : 0 < densityKernelCost Q T c := by
  unfold densityKernelCost
  apply div_pos (mul_pos densityKernelConstant_pos _) hc
  apply Real.rpow_pos_of_pos
  have hq : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  positivity

 theorem density_vertical_height_bound (Q : ℕ) (_hQ : 1 ≤ Q) (T : ℝ) (hT : 1 ≤ T)
    (χ : PrimitiveComplexCharacter) (hχ : χ.modulus ≤ Q) (t : ℝ) (ht : |t| ≤ T) :
    (χ.modulus : ℝ) * (|(densityVerticalPoint (1 / 2) t).im| + 2) ≤ 10 * Q * T := by
  have hq : (χ.modulus : ℝ) ≤ Q := by exact_mod_cast hχ
  have him : (densityVerticalPoint (1 / 2) t).im = 2 * Real.pi * t := by
    simp [densityVerticalPoint]
  rw [him, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hb : 2 * Real.pi * |t| + 2 ≤ 10 * T := by
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  calc
    _ ≤ (χ.modulus : ℝ) * (10 * T) := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ ≤ (Q : ℝ) * (10 * T) := mul_le_mul_of_nonneg_right hq (by positivity)
    _ = _ := by ring

 theorem density_kernel_cost_bound (Q : ℕ) (hQ : 1 ≤ Q) (T c : ℝ)
    (hT : 1 ≤ T) (hc : 0 < c) (χ : PrimitiveComplexCharacter) (hχ : χ.modulus ≤ Q)
    (t : ℝ) (ht : |t| ≤ T) :
    densityKernelConstant *
        ((χ.modulus : ℝ) * (|(densityVerticalPoint (1 / 2) t).im| + 2)) ^ c / c ≤
      densityKernelCost Q T c := by
  unfold densityKernelCost
  apply div_le_div_of_nonneg_right _ hc.le
  apply mul_le_mul_of_nonneg_left _ densityKernelConstant_pos.le
  exact Real.rpow_le_rpow (by positivity)
    (density_vertical_height_bound Q hQ T hT χ hχ t ht) hc.le

 theorem densitySquareKernel_common_bound (Q : ℕ) (hQ : 1 ≤ Q) (T c : ℝ)
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (χ : PrimitiveComplexCharacter) (hχ : χ.modulus ≤ Q) (t u : ℝ) (ht : |t| ≤ T) :
    ‖densitySquareKernel χ (densityVerticalPoint (1 / 2) t)
      ((c : ℂ) + (2 * Real.pi * u : ℝ) * I)‖ ≤
        densityKernelCost Q T c * densityHalfGaussian u := by
  have hs : (densityVerticalPoint (1 / 2) t).re = 1 / 2 := by simp [densityVerticalPoint]
  apply (densitySquareKernel_short_line χ _ hs c (2 * Real.pi * u) hc hc1).trans
  calc
    _ ≤ densityKernelCost Q T c * densityHalfGaussian (2 * Real.pi * u) :=
      mul_le_mul_of_nonneg_right (density_kernel_cost_bound Q hQ T c hT hc χ hχ t ht)
        (densityHalfGaussian_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left (densityHalfGaussian_fourier_scale u)
      (densityKernelCost_pos Q hQ T c hT hc).le

end Ostmann

end OAI
