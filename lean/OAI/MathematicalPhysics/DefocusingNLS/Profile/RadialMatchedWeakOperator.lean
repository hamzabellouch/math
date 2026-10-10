import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedMultiplierLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLowerOrderConvergence

namespace OAI

/-! The actual mass/transport coefficients in the weak spectral operator. The
remaining boundary input is a convergent outgoing Robin matrix. -/

open Filter Topology
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialMatchedWeakOperator (n ell : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hm : radialMatchingMap n z=0) (R : ℝ) (hR : 0 < R)
    (ζ : ℂ) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) :
    SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R :=
  spectralLowerOrderOperator ell R hR
    (spectralRadialWeightMultiplier R (spectralContinuousCoefficient R
      (radialMatchedMassFunction n z) (radialMatchedMassFunction_continuous n z hX hm)))
    (spectralRadialWeightMultiplier R (spectralContinuousCoefficient R
      (radialMatchedTransportFunction n z) (radialMatchedTransportFunction_continuous n z hX hm)))
    ((6-2*radialShootingA n : ℝ) : ℂ) ζ B

noncomputable def radialMatchedLimitWeakOperator (ell : ℕ) (z : ProfileMatchingBall)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ) (hR : 0 < R)
    (ζ : ℂ) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) :
    SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R :=
  spectralLowerOrderOperator ell R hR
    (spectralRadialWeightMultiplier R (spectralContinuousCoefficient R
      (radialMatchedFreeMassFunction z) hc))
    (spectralRadialWeightMultiplier R (spectralContinuousCoefficient R
      (radialMatchedFreeTransportFunction z)
      (continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc)))))
    6 ζ B

theorem radialMatchedWeakOperator_tendsto (ell : ℕ) (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0) (R : ℝ) (hR : 0 < R)
    (ζ : ℂ) (B : ℕ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (B₀ : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hB : Tendsto B atTop (𝓝 B₀)) :
    Tendsto (fun i => radialMatchedWeakOperator (s i) ell (z i) (hX i) (hm i) R hR ζ (B i))
      atTop (𝓝 (radialMatchedLimitWeakOperator ell z₀
        (radialMatchedFreeMassFunction_continuous s hs z z₀ hz hX hm) R hR ζ B₀)) := by
  have hr : Tendsto (fun i => 6-2*radialShootingA (s i)) atTop (𝓝 (6 : ℝ)) := by
    simpa only [Function.comp_def,mul_zero,sub_zero] using
      tendsto_const_nhds.sub ((radialShootingA_tendsto_zero.comp hs.tendsto_atTop).const_mul 2)
  have hc : Tendsto (fun i => ((6-2*radialShootingA (s i) : ℝ) : ℂ)) atTop (𝓝 (6 : ℂ)) := by
    exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  unfold radialMatchedWeakOperator radialMatchedLimitWeakOperator
  apply spectralLowerOrderOperator_tendsto
  · exact radialMatched_massMultiplier_tendsto s hs z z₀ hz hX hm R
  · exact radialMatched_transportMultiplier_tendsto s hs z z₀ hz hX hm R hR.le
  · exact hc
  · exact tendsto_const_nhds
  · exact hB

end DefocusingNLS

end OAI
