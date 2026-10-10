import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalSourceBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedGaugeCoefficients

namespace OAI

/-! The differentiated physical Robin condition gives the actual matched flux condition. -/

namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedPhysical_source_boundary (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 < R)
    (F G f g F₀ G₀ f₀ g₀ : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hpair : ∀ r, (radialMatchedEvenProfile n z r*(f r+Complex.I*g r),
      star (radialMatchedEvenProfile n z r)*(f r-Complex.I*g r))=(F r,G r))
    (hpair₀ : ∀ r, (radialMatchedEvenProfile n z r*(f₀ r+Complex.I*g₀ r),
      star (radialMatchedEvenProfile n z r)*(f₀ r-Complex.I*g₀ r))=(F₀ r,G₀ r))
    (M M' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hM : (deriv F R,deriv G R)=M (F R,G R)+M' (F₀ R,G₀ R)) :
    (spectralGaugeFirstFlux (radialMatchedMassFunction n z)
      (radialMatchedTransportFunction n z) f g R,
     spectralGaugeSecondFlux (radialMatchedMassFunction n z)
      (radialMatchedTransportFunction n z) f g R)=
      spectralFluxBoundary R (radialMatchedMassFunction n z R)
        (radialMatchedTransportFunction n z R)
        (spectralGaugeRobin (radialMatchedProfile n z R) (deriv (radialMatchedProfile n z) R) M)
        (f R,g R)+
      spectralFluxBoundarySlope R (radialMatchedMassFunction n z R)
        (spectralGaugeRobinSlope (radialMatchedProfile n z R) M') (f₀ R,g₀ R) := by
  have hQ := (radialMatchedEvenProfile_contDiff n z hX hz).differentiable (by simp) R
  have hμn : radialMatchedMassFunction n z R ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (radialMatchedProfile_ne_zero n z hX R hR.le))
  have hb := spectralPhysicalGaugeSourceBoundary R (radialMatchedMassFunction n z R)
    (radialMatchedTransportFunction n z R) hR.ne' hμn
    (radialMatchedEvenProfile n z) f g F G f₀ g₀ hQ
    (hf.differentiable (by norm_num) R) (hg.differentiable (by norm_num) R)
    (radialMatchedEvenProfile_ne_zero n z hX R) hpair M M' (by
      rw [hpair₀ R]
      exact hM)
  rw [radialMatchedEvenProfile_nonneg n z R hR.le,
    (radialMatchedEvenProfile_eventuallyEq n z R hR).deriv_eq] at hb
  exact hb

end DefocusingNLS

end OAI
