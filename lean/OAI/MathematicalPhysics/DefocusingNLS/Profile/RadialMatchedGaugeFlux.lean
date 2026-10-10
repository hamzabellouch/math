import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedGaugeCoefficients
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClassicalFluxTesting

namespace OAI

/-! Exact weighted flux equations for a matched-profile gauge eigenmode. -/

open Set
open scoped SchwartzMap
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialMatchedGaugeFirstSource (n : ℕ) (z : ProfileMatchingBall)
    (η lam : ℂ) (f g : ℝ → ℂ) (r : ℝ) : ℂ :=
  η*(r : ℂ)^9*(radialMatchedMassFunction n z r : ℂ)*f r+
    (r : ℂ)^11*(radialMatchedMassFunction n z r : ℂ)*
      (2*((n+radialInnerShootingThreshold : ℕ) : ℂ)*
        ((‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold)) : ℝ) : ℂ)*f r+
      (lam-((6-2*radialShootingA n : ℝ) : ℂ))*g r)

noncomputable def radialMatchedGaugeSecondSource (n : ℕ) (z : ProfileMatchingBall)
    (η lam : ℂ) (f g : ℝ → ℂ) (r : ℝ) : ℂ :=
  η*(r : ℂ)^9*(radialMatchedMassFunction n z r : ℂ)*g r+
    (r : ℂ)^11*(radialMatchedMassFunction n z r : ℂ)*
      (((6-2*radialShootingA n : ℝ) : ℂ)-lam)*f r

theorem radialMatchedGauge_flux (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (η lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsRadialLogGaugeEigenpair (n+radialInnerShootingThreshold)
      (radialMatchedEvenProfile n z) η lam f g) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (spectralGaugeFirstFlux (radialMatchedMassFunction n z)
      (radialMatchedTransportFunction n z) f g)
      (radialMatchedGaugeFirstSource n z η lam f g r) r ∧
    HasDerivAt (spectralGaugeSecondFlux (radialMatchedMassFunction n z)
      (radialMatchedTransportFunction n z) f g)
      (radialMatchedGaugeSecondSource n z η lam f g r) r := by
  obtain ⟨hμ,hA,hlog,hvel⟩ := radialMatchedGauge_coefficients n z hX hz r hr
  obtain ⟨hF,hG⟩ := he r hr
  simp only [add_assoc,hlog,hvel] at hF hG
  have hμn : radialMatchedMassFunction n z r ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (radialMatchedProfile_ne_zero n z hX r hr.le))
  have h := spectralGaugeClassicalFlux (radialMatchedMassFunction n z)
    (radialMatchedTransportFunction n z) f g r
    (2*(star (radialMatchedEvenProfile n z r)*deriv (radialMatchedEvenProfile n z) r).re)
    (6-2*radialShootingA n) η lam
    (2*((n+radialInnerShootingThreshold : ℕ) : ℂ)*
      ((‖radialMatchedEvenProfile n z r‖^(2*(n+radialInnerShootingThreshold)) : ℝ) : ℂ))
    hr.ne' hμn hμ hA
    (hf.differentiable (by norm_num) r) (hg.differentiable (by norm_num) r)
    ((hf.deriv' (n := 1)).differentiable (by norm_num) r)
    ((hg.deriv' (n := 1)).differentiable (by norm_num) r) hF hG
  simpa only [radialMatchedGaugeFirstSource,radialMatchedGaugeSecondSource,
    radialMatchedEvenProfile_nonneg n z r hr.le] using h

theorem radialMatchedGauge_test (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 < R) (η lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsRadialLogGaugeEigenpair (n+radialInnerShootingThreshold)
      (radialMatchedEvenProfile n z) η lam f g) (φ : 𝓢(ℝ,ℂ)) :
    (∫ r in (0 : ℝ)..R, star (deriv φ r)*spectralGaugeFirstFlux
      (radialMatchedMassFunction n z) (radialMatchedTransportFunction n z) f g r)+
      (∫ r in (0 : ℝ)..R, star (φ r)*radialMatchedGaugeFirstSource n z η lam f g r)=
      star (φ R)*spectralGaugeFirstFlux
        (radialMatchedMassFunction n z) (radialMatchedTransportFunction n z) f g R ∧
    (∫ r in (0 : ℝ)..R, star (deriv φ r)*spectralGaugeSecondFlux
      (radialMatchedMassFunction n z) (radialMatchedTransportFunction n z) f g r)+
      (∫ r in (0 : ℝ)..R, star (φ r)*radialMatchedGaugeSecondSource n z η lam f g r)=
      star (φ R)*spectralGaugeSecondFlux
        (radialMatchedMassFunction n z) (radialMatchedTransportFunction n z) f g R := by
  have hμ := radialMatchedMassFunction_continuous n z hX hz
  have hA := radialMatchedTransportFunction_continuous n z hX hz
  have hQ := (radialMatchedProfile_differentiable n z hX hz).continuous
  have hfc := hf.continuous
  have hgc := hg.continuous
  have hDf := hf.continuous_deriv (by norm_num)
  have hDg := hg.continuous_deriv (by norm_num)
  constructor
  · apply spectralClassicalFlux_test R hR.le _ _ _ _ _ _ φ
    · apply Continuous.continuousOn
      unfold spectralGaugeFirstFlux
      fun_prop
    · apply Continuous.continuousOn
      unfold radialMatchedGaugeFirstSource
      fun_prop
    · intro r hr
      exact (radialMatchedGauge_flux n z hX hz η lam f g hf hg he r hr.1).1
    · simp [spectralGaugeFirstFlux]
  · apply spectralClassicalFlux_test R hR.le _ _ _ _ _ _ φ
    · apply Continuous.continuousOn
      unfold spectralGaugeSecondFlux
      fun_prop
    · apply Continuous.continuousOn
      unfold radialMatchedGaugeSecondSource
      fun_prop
    · intro r hr
      exact (radialMatchedGauge_flux n z hX hz η lam f g hf hg he r hr.1).2
    · simp [spectralGaugeSecondFlux]

end DefocusingNLS

end OAI
