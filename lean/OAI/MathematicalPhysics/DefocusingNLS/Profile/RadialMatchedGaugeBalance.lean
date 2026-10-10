import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedGaugeFlux
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeightedFluxBalance

namespace OAI

/-! The actual matched-profile eigenmode satisfies both weighted weak balances. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS
open ProfileCertificate

theorem spectralClassicalRadialPairing_const_weight (R k : ℝ) (q : ℝ → ℝ)
    (f φ : ℝ → ℂ) :
    spectralClassicalRadialPairing R (fun r => k*q r) f φ=
      (k : ℂ)*spectralClassicalRadialPairing R q f φ := by
  unfold spectralClassicalRadialPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun r => by
    simp only [Complex.real_smul,Complex.ofReal_mul]
    ring)

theorem radialMatchedGauge_balance (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 < R) (η lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsRadialLogGaugeEigenpair (n+radialInnerShootingThreshold)
      (radialMatchedEvenProfile n z) η lam f g) (φ : 𝓢(ℝ,ℂ)) :
    (spectralClassicalRadialPairing R (radialMatchedMassFunction n z) (deriv f) (deriv φ)+
      η*spectralClassicalAngularPairing R (radialMatchedMassFunction n z) f φ+
      ((radialShootingA n)⁻¹ : ℝ)*spectralClassicalRadialPairing R
        (fun r => radialMatchedMassFunction n z r*
          ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold))) f φ=
      (((6-2*radialShootingA n : ℝ) : ℂ)-lam)*
        spectralClassicalRadialPairing R (radialMatchedMassFunction n z) g φ+
      spectralClassicalRadialPairing R (radialMatchedTransportFunction n z) g (deriv φ)+
      star (φ R)*spectralGaugeFirstFlux (radialMatchedMassFunction n z)
        (radialMatchedTransportFunction n z) f g R) ∧
    (spectralClassicalRadialPairing R (radialMatchedMassFunction n z) (deriv g) (deriv φ)+
      η*spectralClassicalAngularPairing R (radialMatchedMassFunction n z) g φ+
      (((6-2*radialShootingA n : ℝ) : ℂ)-lam)*
        spectralClassicalRadialPairing R (radialMatchedMassFunction n z) f φ+
      spectralClassicalRadialPairing R (radialMatchedTransportFunction n z) f (deriv φ)=
      star (φ R)*spectralGaugeSecondFlux (radialMatchedMassFunction n z)
        (radialMatchedTransportFunction n z) f g R) := by
  have hμ := radialMatchedMassFunction_continuous n z hX hz
  have hA := radialMatchedTransportFunction_continuous n z hX hz
  have hQ := (radialMatchedProfile_differentiable n z hX hz).continuous
  obtain ⟨hfirst,hsecond⟩ := radialMatchedGauge_test n z hX hz R hR η lam f g hf hg he φ
  constructor
  · have hp : Continuous (fun r => 2*((n+radialInnerShootingThreshold : ℕ) : ℝ)*
        ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold))) := by fun_prop
    have ht := spectralWeightedFlux_first_balance R hR.le
      (radialMatchedMassFunction n z) (radialMatchedTransportFunction n z)
      (fun r => 2*((n+radialInnerShootingThreshold : ℕ) : ℝ)*
        ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold)))
      hμ hA hp f g hf hg η ((6-2*radialShootingA n : ℝ) : ℂ) lam φ (by
        simpa only [radialMatchedGaugeFirstSource,Complex.ofReal_mul,Complex.ofReal_ofNat,
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
  · exact spectralWeightedFlux_second_balance R hR.le
      (radialMatchedMassFunction n z) (radialMatchedTransportFunction n z) hμ hA
      f g hf hg η ((6-2*radialShootingA n : ℝ) : ℂ) lam φ (by
        simpa only [radialMatchedGaugeSecondSource] using hsecond)

end DefocusingNLS

end OAI
