import OAI.NumberTheory.Ostmann.ZeroDensity.DensityNormalizedEquation
import OAI.NumberTheory.Ostmann.Characters.CharacterCompletedDivergence

namespace OAI

/-! # The normalized right-hand kernel in the square functional equation -/

namespace Ostmann

open Complex MeasureTheory

noncomputable def densitySquareKernel (χ : PrimitiveComplexCharacter) (s w : ℂ) : ℂ :=
  densityCompletedSquareWeight χ s w / w

 theorem densitySmoothedSquare_integral (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) :
    densitySmoothedSquare χ s = (2 * (Real.pi : ℂ))⁻¹ *
      ∫ u : ℝ, densitySquareKernel χ s (1 + u * I) * χ.L (s + (1 + u * I)) ^ 2 := by
  unfold densitySmoothedSquare densitySquareIntegral
  rw [mul_div_assoc, ← integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  have hp : 0 < s.re := by linarith
  have hu : 0 < (s + (1 + (u : ℂ) * I)).re := by norm_num [hs]
  calc
    _ = (densitySquareGaussian χ s (1 + u * I) / densitySquareNormalizer χ s) /
        (1 + u * I) := by unfold densitySquareContour; ring
    _ = _ := by rw [densitySquareGaussian_normalized χ s _ hp hu]; unfold densitySquareKernel; ring

 theorem densitySquareKernel_line_bound (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (u : ℝ) :
    ‖densitySquareKernel χ s (1 + u * I)‖ ≤
      (Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
        2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
        ((χ.modulus : ℝ) * (|s.im| + 2))) * Real.exp (-(u ^ 2) / 2) := by
  have hn : 1 ≤ ‖(1 : ℂ) + u * I‖ := by
    simpa using Complex.re_le_norm ((1 : ℂ) + u * I)
  rw [densitySquareKernel, norm_div]
  apply (div_le_self (norm_nonneg _) hn).trans
  have h := densityCompletedSquareWeight_bound χ s (1 + u * I) hs
    (by norm_num) (by norm_num)
  simpa using h

 theorem densitySquareKernel_line_continuous (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) : Continuous (fun u : ℝ => densitySquareKernel χ s (1 + u * I)) := by
  have hΓ : Continuous (fun u : ℝ =>
      DirichletCharacter.gammaFactor χ.character (s + (1 + (u : ℂ) * I))) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    apply (χ.gammaFactor_differentiableAt_pos _ (by norm_num [hs])).continuousAt.comp
    fun_prop
  unfold densitySquareKernel densityCompletedSquareWeight
  apply Continuous.div
  · apply Continuous.mul
    · apply Continuous.mul
      · have hq : (χ.modulus : ℂ) ≠ 0 := by exact_mod_cast χ.positive.ne'
        exact (differentiable_id.const_cpow (Or.inl hq)).continuous.comp (by fun_prop)
      · exact (hΓ.div_const _).pow 2
    · fun_prop
  · fun_prop
  · intro u h
    have hr := congrArg Complex.re h
    norm_num at hr

end Ostmann

end OAI
