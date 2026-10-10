import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakCoefficients
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeGaugeExtension
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFluxSmoothness
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeCollarUniqueness
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeRobinPropagation

namespace OAI

/-! The same weak kernel has the free physical equation throughout the open exterior. -/

open Set
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialMatchedWeak_physical_hasDerivAt (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (w : SpectralHarmonicWeight R) (hw : w.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) (u : SpectralHarmonicPair ell R)
    (he : let hR := (radialMatchedCore_radius_pos z).trans hLR
      ∀ v : spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)),
        spectralHarmonicPairComplexForm ell R w u v=
          inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
            (spectralHarmonicObservation ell R hR u)) v) :
    let hR := (radialMatchedCore_radius_pos z).trans hLR
    let X := spectralPhysicalGaugePair (radialShootingFreeExterior z)
      (spectralHarmonicRepresentative ell R hR u.fst)
      (spectralHarmonicRepresentative ell R hR u.snd)
    ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R,
      HasDerivAt X (spectralFreePhysicalPairField (radialShootingB (profileMatchingParameter z)) ζ
        ((ell : ℂ)*((ell : ℂ)+10)) r (X r)) r := by
  dsimp only at he ⊢
  let hR := (radialMatchedCore_radius_pos z).trans hLR
  let a := spectralContinuousCoefficient R (radialMatchedFreeTransportFunction z)
    (continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc)))
  have hwc : Continuous w.density := by rw [hw]; exact hc
  have hac : Continuous a.density :=
    continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc))
  have hp (r : ℝ) (hr : 0 ≤ r) : 0 < w.density r := by
    rw [hw]
    exact radialMatchedFreeMass_pos z r hr
  have he' := radialMatchedWeak_equation ell z hc R
    (radialShootingR (profileMatchingParameter z)) hR w a hw rfl ζ B u he
  have haD : a.density=radialMatchedFreeTransportFunction z := rfl
  let U := spectralFluxState ell R hR w a u
  have hU : ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R,
      HasDerivAt U (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U r)) r := by
    intro r hr
    simpa only [hw,haD] using spectralFluxState_hasDerivAt ell R
      (radialShootingR (profileMatchingParameter z)) hR (radialMatchedCore_radius_pos z)
      w a u 6 ζ B hwc.continuousOn hac.continuousOn (fun r hr => hp r hr.1.le) he' r hr
  exact radialMatchedFreeGaugeExtension_hasDerivAt ell z hz₁ hz hc R
    (radialShootingR (profileMatchingParameter z)) le_rfl ζ U hU _ _
    (fun _ _ => rfl) (fun _ _ => rfl)

end DefocusingNLS

end OAI
