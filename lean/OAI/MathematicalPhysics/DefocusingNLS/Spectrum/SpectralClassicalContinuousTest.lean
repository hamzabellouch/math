import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClassicalFluxTesting

namespace OAI

/-! A classical flux can be tested against its own C¹ eigenfunction;
compact support is unnecessary on the finite radial interval. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralClassicalFlux_continuous_test (R : ℝ) (hR : 0 ≤ R) (F H φ : ℝ → ℂ)
    (hF : ContinuousOn F (Icc 0 R)) (hH : ContinuousOn H (Icc 0 R))
    (hD : ∀ r ∈ Ioo 0 R, HasDerivAt F (H r) r) (h0 : F 0=0)
    (hφ : ContDiff ℝ 1 φ) :
    (∫ r in (0 : ℝ)..R, star (deriv φ r)*F r)+
      (∫ r in (0 : ℝ)..R, star (φ r)*H r)=star (φ R)*F R := by
  have he : (∫ r in (0 : ℝ)..R, star (φ r)*H r)=
      star (φ R)*F R-star (φ 0)*F 0-
        ∫ r in (0 : ℝ)..R, star (deriv φ r)*F r := by
    apply intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    · simpa only [uIcc_of_le hR] using hφ.continuous.star.continuousOn (s := Icc 0 R)
    · simpa only [uIcc_of_le hR] using hF
    · intro r _
      exact ((hφ.differentiable (by norm_num) r).hasDerivAt).star
    · intro r hr
      exact hD r (by simpa only [min_eq_left hR,max_eq_right hR] using hr)
    · exact (hφ.continuous_deriv (by norm_num)).star.intervalIntegrable 0 R
    · exact hH.intervalIntegrable_of_Icc hR
  rw [h0,mul_zero,sub_zero] at he
  linear_combination he

end DefocusingNLS

end OAI
