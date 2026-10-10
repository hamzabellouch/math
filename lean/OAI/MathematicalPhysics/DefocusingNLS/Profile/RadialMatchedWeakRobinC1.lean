import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakCoefficients
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFluxSmoothness
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeakRobinC1

namespace OAI

/-! The actual weak equation gives a C1 endpoint extension with opaque boundary data. -/

open Set
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedWeak_robin_C1 (ell : ℕ) (z : ProfileMatchingBall)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (δ : ℝ) (hlδ : radialShootingR (profileMatchingParameter z) < δ) (hδR : δ < R)
    (w : SpectralHarmonicWeight R) (hw : w.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (M B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hB : B=spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
      (radialMatchedFreeTransportFunction z R) M)
    (u : SpectralHarmonicPair ell R)
    (he : let hR := (radialMatchedCore_radius_pos z).trans hLR
      ∀ v : spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)),
        spectralHarmonicPairComplexForm ell R w u v=
          inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
            (spectralHarmonicObservation ell R hR u)) v) :
    let hR := (radialMatchedCore_radius_pos z).trans hLR
    ∃ f g : ℝ → ℂ, Continuous f ∧ Continuous g ∧
      ContinuousOn (deriv f) (Icc δ R) ∧ ContinuousOn (deriv g) (Icc δ R) ∧
      EqOn f (spectralHarmonicRepresentative ell R hR u.fst) (Icc δ R) ∧
      EqOn g (spectralHarmonicRepresentative ell R hR u.snd) (Icc δ R) ∧
      (deriv f R,deriv g R)=M (f R,g R) := by
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
  have hb : B=spectralFluxBoundary R (w.density R) (a.density R) M := by
    rw [hw]
    exact hB
  apply spectralWeakEquation_robin_C1 ell R (radialShootingR (profileMatchingParameter z))
    δ hR (radialMatchedCore_radius_pos z) hlδ hδR w a u 6 ζ M
    hwc.continuousOn hac.continuousOn hwc.continuousOn hac.continuousOn
    (fun r hr => hp r hr.1.le)
    (fun r hr => hp r (((radialMatchedCore_radius_pos z).trans hlδ).le.trans hr.1))
  rw [← hb]
  exact he'

end DefocusingNLS

end OAI
