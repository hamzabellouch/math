import OAI.NumberTheory.Ostmann.ZeroDensity.DensityKernelStrip
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityGaussianCauchy

namespace OAI

/-! # The short-line kernel bound retaining its exact conductor exponent -/

namespace Ostmann

open Complex

 theorem densitySquareKernel_short_line (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (c u : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ‖densitySquareKernel χ s ((c : ℂ) + u * I)‖ ≤
      (Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
        2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
        ((χ.modulus : ℝ) * (|s.im| + 2)) ^ c / c) * densityHalfGaussian u := by
  have hb := densityCompletedSquareWeight_bound χ s ((c : ℂ) + u * I) hs
    (by simp; linarith) (by simp; linarith)
  have he : ((c : ℂ) + u * I).re = c := by simp
  have hi : ((c : ℂ) + u * I).im = u := by simp
  rw [he, hi] at hb
  have hn : c ≤ ‖(c : ℂ) + u * I‖ := by simpa only [he] using Complex.re_le_norm ((c : ℂ) + u * I)
  rw [densitySquareKernel, norm_div]
  apply (div_le_div_of_nonneg_left (norm_nonneg _) hc hn).trans
  have hd := div_le_div_of_nonneg_right hb hc.le
  unfold densityHalfGaussian
  convert hd using 1
  ring

end Ostmann

end OAI
