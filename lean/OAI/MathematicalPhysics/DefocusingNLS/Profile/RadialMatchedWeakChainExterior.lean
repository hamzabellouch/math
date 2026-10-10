import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakChainFlux
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakExterior
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeChainGaugeExtension

namespace OAI

/-! The actual weak first chain satisfies the forced physical equation. -/

open Set
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedWeak_chain_physical_hasDerivAt (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (w : SpectralHarmonicWeight R) (hw : w.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (u₀ u₁ : SpectralHarmonicPair ell R)
    (he₀ : let hR := (radialMatchedCore_radius_pos z).trans hLR
      ∀ v : spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)),
        spectralHarmonicPairComplexForm ell R w u₀ v =
          inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
            (spectralHarmonicObservation ell R hR u₀)) v)
    (he₁ : let hR := (radialMatchedCore_radius_pos z).trans hLR
      ∀ v : spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)),
        spectralHarmonicPairComplexForm ell R w u₁ v =
          inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
            (spectralHarmonicObservation ell R hR u₁) +
            spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B'
              (spectralHarmonicObservation ell R hR u₀)) v) :
    let hR := (radialMatchedCore_radius_pos z).trans hLR
    let Q := radialShootingFreeExterior z
    let X₀ := spectralPhysicalGaugePair Q (spectralHarmonicRepresentative ell R hR u₀.fst)
      (spectralHarmonicRepresentative ell R hR u₀.snd)
    let X₁ := spectralPhysicalGaugePair Q (spectralHarmonicRepresentative ell R hR u₁.fst)
      (spectralHarmonicRepresentative ell R hR u₁.snd)
    ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R, HasDerivAt X₁
      (spectralFreePhysicalPairField (radialShootingB (profileMatchingParameter z)) ζ
        ((ell : ℂ)*((ell : ℂ)+10)) r (X₁ r) + spectralFreeChainSource (X₀ r)) r := by
  dsimp only at he₀ he₁ ⊢
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
  have he₀' := radialMatchedWeak_equation ell z hc R L hR w a hw rfl ζ B u₀ he₀
  have haD : a.density=radialMatchedFreeTransportFunction z := rfl
  let U₀ := spectralFluxState ell R hR w a u₀
  let U₁ := spectralFluxState ell R hR w a u₁
  have hU₀ : ∀ r ∈ Ioo L R, HasDerivAt U₀
      (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U₀ r)) r := by
    intro r hr
    simpa only [hw,haD] using spectralFluxState_hasDerivAt ell R L hR hL w a u₀ 6 ζ B
      hwc.continuousOn hac.continuousOn (fun t ht => hp t ht.1.le) he₀' r hr
  have hU₁ := radialMatchedWeak_chain_flux_hasDerivAt ell z hc R hLR w hw ζ B B' u₀ u₁ he₁
  exact radialMatchedFreeGaugeExtension_chain_hasDerivAt ell z hz₁ hz hc R L le_rfl ζ U₀ U₁
    hU₀ hU₁ _ _ (fun _ _ => rfl) (fun _ _ => rfl)

end DefocusingNLS

end OAI
