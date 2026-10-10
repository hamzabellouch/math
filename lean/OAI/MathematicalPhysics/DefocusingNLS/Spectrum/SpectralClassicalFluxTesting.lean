import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeClassicalFlux
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAngularComplexIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

namespace OAI

/-! The radial divergence equation yields its weak identity including the outer trace. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralClassicalFlux_test (R : ℝ) (hR : 0 ≤ R) (F H : ℝ → ℂ)
    (hF : ContinuousOn F (Icc 0 R)) (hH : ContinuousOn H (Icc 0 R))
    (hD : ∀ r ∈ Ioo 0 R, HasDerivAt F (H r) r) (h0 : F 0=0)
    (φ : 𝓢(ℝ,ℂ)) :
    (∫ r in (0 : ℝ)..R, star (deriv φ r)*F r)+
      (∫ r in (0 : ℝ)..R, star (φ r)*H r)=star (φ R)*F R := by
  have he : (∫ r in (0 : ℝ)..R, star (φ r)*H r)=
      star (φ R)*F R-star (φ 0)*F 0-
        ∫ r in (0 : ℝ)..R, star (deriv φ r)*F r := by
    apply intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    · simpa only [uIcc_of_le hR] using φ.continuous.star.continuousOn (s := Icc 0 R)
    · simpa only [uIcc_of_le hR] using hF
    · intro r _
      exact (φ.hasDerivAt r).star
    · intro r hr
      exact hD r (by simpa only [min_eq_left hR,max_eq_right hR] using hr)
    · exact ((SchwartzMap.derivCLM ℂ ℂ φ).continuous.star).intervalIntegrable 0 R
    · exact hH.intervalIntegrable_of_Icc hR
  rw [h0,mul_zero,sub_zero] at he
  linear_combination he

end DefocusingNLS

end OAI
