import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedSourceFlux
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeightedSourceBalance
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedGaugeBalance

namespace OAI

/-! The actual generalized radial mode satisfies the completed weak source balance. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedSource_balance (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 < R) (η lam : ℂ) (f g F G : ℝ → ℂ)
    (hF : Continuous F) (hG : Continuous G)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsRadialLogGaugeSourcePair (n+radialInnerShootingThreshold)
      (radialMatchedEvenProfile n z) η lam f g F G) (φ : 𝓢(ℝ,ℂ)) :
    (spectralClassicalRadialPairing R (radialMatchedMassFunction n z) (deriv f) (deriv φ)+
      η*spectralClassicalAngularPairing R (radialMatchedMassFunction n z) f φ+
      ((radialShootingA n)⁻¹ : ℝ)*spectralClassicalRadialPairing R
        (fun r => radialMatchedMassFunction n z r*
          ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold))) f φ+
      spectralClassicalRadialPairing R (radialMatchedMassFunction n z) G φ=
      (((6-2*radialShootingA n : ℝ) : ℂ)-lam)*
        spectralClassicalRadialPairing R (radialMatchedMassFunction n z) g φ+
      spectralClassicalRadialPairing R (radialMatchedTransportFunction n z) g (deriv φ)+
      star (φ R)*spectralGaugeFirstFlux (radialMatchedMassFunction n z)
        (radialMatchedTransportFunction n z) f g R) ∧
    (spectralClassicalRadialPairing R (radialMatchedMassFunction n z) (deriv g) (deriv φ)+
      η*spectralClassicalAngularPairing R (radialMatchedMassFunction n z) g φ+
      (((6-2*radialShootingA n : ℝ) : ℂ)-lam)*
        spectralClassicalRadialPairing R (radialMatchedMassFunction n z) f φ+
      spectralClassicalRadialPairing R (radialMatchedTransportFunction n z) f (deriv φ)-
      spectralClassicalRadialPairing R (radialMatchedMassFunction n z) F φ=
      star (φ R)*spectralGaugeSecondFlux (radialMatchedMassFunction n z)
        (radialMatchedTransportFunction n z) f g R) := by
  have hμ := radialMatchedMassFunction_continuous n z hX hz
  have hA := radialMatchedTransportFunction_continuous n z hX hz
  have hQ := (radialMatchedProfile_differentiable n z hX hz).continuous
  obtain ⟨hfirst,hsecond⟩ := radialMatchedSource_test n z hX hz R hR η lam f g F G hF hG hf hg he φ
  constructor
  · have hp : Continuous (fun r => 2*((n+radialInnerShootingThreshold : ℕ) : ℝ)*
        ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold))) := by fun_prop
    have ht := spectralWeightedFlux_first_source_balance R hR.le
      (radialMatchedMassFunction n z) (radialMatchedTransportFunction n z)
      (fun r => 2*((n+radialInnerShootingThreshold : ℕ) : ℝ)*
        ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold)))
      hμ hA hp f g G hG hf hg η ((6-2*radialShootingA n : ℝ) : ℂ) lam φ (by
        simpa only [radialMatchedForcedFirstSource,Complex.ofReal_mul,Complex.ofReal_ofNat,
          Complex.ofReal_natCast]
          using hfirst)
    have hfactor : (radialShootingA n)⁻¹=2*((n+radialInnerShootingThreshold : ℕ) : ℝ) := by
      simp [radialShootingA,one_div]
    have hpEq : (fun r => radialMatchedMassFunction n z r*
        (2*((n+radialInnerShootingThreshold : ℕ) : ℝ)*
          ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold))))=
        (fun r => (radialShootingA n)⁻¹*(radialMatchedMassFunction n z r*
          ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold)))) := by
      funext r
      rw [hfactor]
      ring
    rw [hpEq,spectralClassicalRadialPairing_const_weight] at ht
    exact ht
  · exact spectralWeightedFlux_second_source_balance R hR.le
      (radialMatchedMassFunction n z) (radialMatchedTransportFunction n z) hμ hA
      f g F hF hf hg η ((6-2*radialShootingA n : ℝ) : ℂ) lam φ (by
        simpa only [radialMatchedForcedSecondSource] using hsecond)

end DefocusingNLS

end OAI
