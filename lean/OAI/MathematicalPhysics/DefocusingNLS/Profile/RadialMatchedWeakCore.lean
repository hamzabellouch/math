import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFluxSmoothness
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakCoefficients
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCoreBoundary

namespace OAI

/-! Core information for the same weak vector used in exterior propagation. -/

open Set
open scoped SchwartzMap
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedWeak_core (ell : ℕ) (z : ProfileMatchingBall)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (w : SpectralHarmonicWeight R) (hw : w.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) (u : SpectralHarmonicPair ell R)
    (hu : u ∈ spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)))
    (he : ∀ v : spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)),
      spectralHarmonicPairComplexForm ell R w u v=
        inner ℂ (radialMatchedLimitWeakOperator ell z hc R
          ((radialMatchedCore_radius_pos z).trans hLR) ζ B
          (spectralHarmonicObservation ell R ((radialMatchedCore_radius_pos z).trans hLR) u)) v) :
    let hR := (radialMatchedCore_radius_pos z).trans hLR
    (∀ r ∈ Ioc 0 (radialShootingR (profileMatchingParameter z)),
      spectralHarmonicRepresentative ell R hR u.fst r=0) ∧
    ContinuousOn (deriv (spectralHarmonicRepresentative ell R hR u.snd)) (Ioo 0 R) ∧
    ∃ C : ℂ, (∀ r ∈ Ioc 0 (radialShootingR (profileMatchingParameter z)),
      spectralHarmonicRepresentative ell R hR u.snd r=C*(r : ℂ)^ell) ∧
      deriv (spectralHarmonicRepresentative ell R hR u.snd)
        (radialShootingR (profileMatchingParameter z))=
        (ell : ℂ)*spectralHarmonicRepresentative ell R hR u.snd
          (radialShootingR (profileMatchingParameter z))/
          (radialShootingR (profileMatchingParameter z) : ℂ) := by
  dsimp only
  let L := radialShootingR (profileMatchingParameter z)
  let hR := (radialMatchedCore_radius_pos z).trans hLR
  let a := spectralContinuousCoefficient R (radialMatchedFreeTransportFunction z)
    (continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc)))
  have he' : ∀ f : 𝓢(ℝ,ℂ),
      spectralHarmonicPairComplexForm ell R w u (spectralSecondTest ell R f)=
        inner ℂ (spectralLowerOrderOperator ell R hR
          (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) 6 ζ B
          (spectralHarmonicObservation ell R hR u)) (spectralSecondTest ell R f) := by
    intro f
    exact (he ⟨spectralSecondTest ell R f,spectralSecondTest_core ell R L f⟩).trans
      (congrArg (fun (K : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R) => inner ℂ (K (spectralHarmonicObservation ell R hR u))
        (spectralSecondTest ell R f))
        (radialMatchedLimitWeakOperator_eq ell z hc R hR w a hw rfl ζ B))
  have hwc : ContinuousOn w.density (Ioo 0 R) := by rw [hw]; exact hc.continuousOn
  have hac : ContinuousOn a.density (Ioo 0 R) :=
    (continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc))).continuousOn
  have hp (r : ℝ) (hr : r ∈ Ioo 0 R) : 0 < w.density r := by
    rw [hw]
    exact radialMatchedFreeMass_pos z r hr.1.le
  have hc0 (r : ℝ) (hr : r ∈ Ioc 0 L) : w.density r=1 := by
    rw [hw]
    exact radialMatchedFreeMass_core z r hr.2
  exact ⟨(fun r hr => spectralHarmonicCore_representative_zero ell R L hR hLR.le u hu r hr),
    (spectralSecond_classical ell R hR w a u 6 ζ B hwc hac hp he').2.1,
    spectralSecond_core_power ell R L hR (radialMatchedCore_radius_pos z) hLR w a u
      6 ζ B hu hwc hac hp hc0 he'⟩

end DefocusingNLS

end OAI
