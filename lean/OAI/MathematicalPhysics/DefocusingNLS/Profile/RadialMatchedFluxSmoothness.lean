import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPencilFluxSystem
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedTransportSmoothness
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCoreBoundary

namespace OAI

/-! Actual limiting kernel vectors have smooth flux states on the free far field. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedCore_radius_pos (z : ProfileMatchingBall) :
    0 < radialShootingR (profileMatchingParameter z) :=
  lt_of_lt_of_le (by norm_num) (radialShooting_geometry (profileMatchingParameter z)).2.1

theorem radialMatchedLimit_kernel_smooth (ell : ℕ) (z : ProfileMatchingBall)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (s : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z)))
    (hmass : s.limitWeight.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) (v : SpectralRadialObservationSpace R)
    (hv : s.limitPencil ell (radialMatchedCore_radius_pos z) hLR
      (radialMatchedLimitWeakOperator ell z hc R ((radialMatchedCore_radius_pos z).trans hLR) ζ B) v=v) :
    let hR := (radialMatchedCore_radius_pos z).trans hLR
    let a := spectralContinuousCoefficient R (radialMatchedFreeTransportFunction z)
      (continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc)))
    ∃ u : SpectralHarmonicPair ell R,
      u ∈ spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)) ∧
      spectralHarmonicObservation ell R hR u=v ∧
      (∀ x ∈ Ioo (radialShootingR (profileMatchingParameter z)) R,
        HasDerivAt (spectralFluxState ell R hR s.limitWeight a u)
          (spectralFluxField ell (s.limitWeight.density x) (a.density x) 6 ζ x
            (spectralFluxState ell R hR s.limitWeight a u x)) x) ∧
      ∀ α β : ℝ, innerBoundaryRadius < α → β < R →
        ContDiffOn ℝ ∞ (spectralFluxState ell R hR s.limitWeight a u) (Icc α β) := by
  dsimp only
  let a := spectralContinuousCoefficient R (radialMatchedFreeTransportFunction z)
    (continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc)))
  have hQ := spectralRadialWeightMultiplier_eq_of_density R s.limitWeight
    (spectralContinuousCoefficient R (radialMatchedFreeMassFunction z) hc) hmass
  have hw : ContinuousOn s.limitWeight.density (Ioo 0 R) := by rw [hmass]; exact hc.continuousOn
  have ha : ContinuousOn a.density (Ioo 0 R) :=
    (continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc))).continuousOn
  have hp (x : ℝ) (hx : x ∈ Ioo 0 R) : 0 < s.limitWeight.density x := by
    rw [hmass]
    exact radialMatchedFreeMass_pos z x hx.1.le
  obtain ⟨u,hu,hobs,hode,hsmooth⟩ := s.limitPencil_flux_system ell
    (radialMatchedCore_radius_pos z) hLR a 6 ζ B hw ha hp v (by
      simpa only [hQ,radialMatchedLimitWeakOperator,a] using hv)
  refine ⟨u,hu,hobs,hode,fun α β hα hβ => ?_⟩
  apply hsmooth α β
    ((radialShooting_geometry (profileMatchingParameter z)).2.2.2.1.trans_lt hα) hβ
  · rw [hmass]
    exact (radialMatchedFreeMass_contDiffOn_exterior z).mono (fun _ hx => hα.trans_le hx.1)
  · exact radialMatchedFreeTransport_contDiffOn_annulus z hc α β hα

end DefocusingNLS

end OAI
