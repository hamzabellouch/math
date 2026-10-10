import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakForcedEquation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFluxSmoothness
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainFluxSystem

namespace OAI

/-! The actual weak derivative load gives the forced exterior flux system. -/

open Set
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedWeak_chain_flux_hasDerivAt (ell : ℕ) (z : ProfileMatchingBall)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (w : SpectralHarmonicWeight R) (hw : w.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (u₀ u₁ : SpectralHarmonicPair ell R)
    (he₁ : let hR := (radialMatchedCore_radius_pos z).trans hLR
      ∀ v : spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)),
        spectralHarmonicPairComplexForm ell R w u₁ v =
          inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
            (spectralHarmonicObservation ell R hR u₁) +
            spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B'
              (spectralHarmonicObservation ell R hR u₀)) v) :
    let hR := (radialMatchedCore_radius_pos z).trans hLR
    let a := spectralContinuousCoefficient R (radialMatchedFreeTransportFunction z)
      (continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc)))
    let U₀ := spectralFluxState ell R hR w a u₀
    let U₁ := spectralFluxState ell R hR w a u₁
    ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R, HasDerivAt U₁
      (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U₁ r) +
        spectralFluxFieldSlope (radialMatchedFreeMassFunction z r) r (U₀ r)) r := by
  dsimp only at he₁ ⊢
  let L := radialShootingR (profileMatchingParameter z)
  have hL : 0 < L := radialMatchedCore_radius_pos z
  let hR := hL.trans hLR
  let a := spectralContinuousCoefficient R (radialMatchedFreeTransportFunction z)
    (continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc)))
  have hwc : Continuous w.density := by rw [hw]; exact hc
  have hac : Continuous a.density :=
    continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc))
  have hp (r : ℝ) (hr : 0 ≤ r) : 0 < w.density r := by
    rw [hw]
    exact radialMatchedFreeMass_pos z r hr
  let F : SpectralHarmonicPair ell R := spectralLowerOrderSlope ell R hR
    (spectralRadialWeightMultiplier R w) B' (spectralHarmonicObservation ell R hR u₀)
  have heF : ∀ v : spectralHarmonicCoreSubspace ell R L,
      spectralHarmonicPairComplexForm ell R w u₁ v =
        inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
          (spectralHarmonicObservation ell R hR u₁)+F) v := by
    simpa only [F,L,hR] using he₁
  have he₁' := radialMatchedWeak_forced_equation ell z hc R L hR w a hw rfl F ζ B u₁ heF
  have haD : a.density=radialMatchedFreeTransportFunction z := rfl
  let U₀ := spectralFluxState ell R hR w a u₀
  let U₁ := spectralFluxState ell R hR w a u₁
  have hU₁ : ∀ r ∈ Ioo L R, HasDerivAt U₁
      (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U₁ r) +
        spectralFluxFieldSlope (radialMatchedFreeMassFunction z r) r (U₀ r)) r := by
    intro r hr
    simpa only [hw,haD] using spectralFluxState_chain_hasDerivAt ell R L hR hL w a u₀ u₁ 6 ζ B B'
      hwc.continuousOn hac.continuousOn (fun t ht => hp t ht.1.le) he₁' r hr
  exact hU₁

end DefocusingNLS

end OAI
