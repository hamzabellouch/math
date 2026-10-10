import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPencilRobin
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFluxSmoothness

namespace OAI

/-! The matched limiting pencil has the physical outgoing Robin boundary condition. -/

open Set
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedLimit_kernel_robin (ell : ℕ) (z : ProfileMatchingBall)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (δ : ℝ) (hlδ : radialShootingR (profileMatchingParameter z) < δ) (hδR : δ < R)
    (s : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z)))
    (hmass : s.limitWeight.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (M : ℂ × ℂ →L[ℂ] ℂ × ℂ) (v : SpectralRadialObservationSpace R)
    (hv : let hR := (radialMatchedCore_radius_pos z).trans hLR
      let Q := radialMatchedFreeProfile z
      s.limitPencil ell (radialMatchedCore_radius_pos z) hLR
        (radialMatchedLimitWeakOperator ell z hc R hR ζ
          (spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
            (radialMatchedFreeTransportFunction z R) (spectralGaugeRobin (Q R) (deriv Q R) M))) v=v) :
    let hR := (radialMatchedCore_radius_pos z).trans hLR
    let Q := radialMatchedFreeProfile z
    ∃ u : SpectralHarmonicPair ell R,
      u ∈ spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)) ∧
      spectralHarmonicObservation ell R hR u=v ∧
      ∃ f g : ℝ → ℂ, Continuous f ∧ Continuous g ∧
        EqOn f (spectralHarmonicRepresentative ell R hR u.fst) (Icc δ R) ∧
        EqOn g (spectralHarmonicRepresentative ell R hR u.snd) (Icc δ R) ∧
        spectralGaugeColumns (Q R) (deriv f R,deriv g R)+
          spectralGaugeColumns (deriv Q R) (f R,g R)=M (spectralGaugeColumns (Q R) (f R,g R)) := by
  dsimp only at hv ⊢
  let a := spectralContinuousCoefficient R (radialMatchedFreeTransportFunction z)
    (continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc)))
  have hR := (radialMatchedCore_radius_pos z).trans hLR
  have hQ := spectralRadialWeightMultiplier_eq_of_density R s.limitWeight
    (spectralContinuousCoefficient R (radialMatchedFreeMassFunction z) hc) hmass
  have hw : ContinuousOn s.limitWeight.density (Ioo 0 R) := by rw [hmass]; exact hc.continuousOn
  have hwc : ContinuousOn s.limitWeight.density (Icc δ R) := by rw [hmass]; exact hc.continuousOn
  have ha : Continuous a.density :=
    continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc))
  have haD : a.density=radialMatchedFreeTransportFunction z := rfl
  have hp (x : ℝ) (hx : 0 ≤ x) : 0 < s.limitWeight.density x := by
    rw [hmass]
    exact radialMatchedFreeMass_pos z x hx
  have hq : radialMatchedFreeProfile z R ≠ 0 := by
    intro hz
    have h := radialMatchedFreeMass_pos z R hR.le
    simp only [radialMatchedFreeMassFunction,hz,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),lt_self_iff_false] at h
  obtain ⟨u,hu,hobs,f,g,hf,hg,hef,heg,hboundary⟩ := s.limitPencil_robin ell
    (radialMatchedCore_radius_pos z) hLR δ hlδ hδR a 6 ζ
    (spectralGaugeRobin (radialMatchedFreeProfile z R) (deriv (radialMatchedFreeProfile z) R) M)
    hw ha.continuousOn hwc ha.continuousOn (fun x hx => hp x hx.1.le)
    (fun x hx => hp x (((radialMatchedCore_radius_pos z).trans hlδ).le.trans hx.1)) v (by
      rw [hQ,hmass,haD]
      exact hv)
  refine ⟨u,hu,hobs,f,g,hf,hg,hef,heg,?_⟩
  exact (spectralGaugeRobin_condition _ _ hq M (f R,g R) (deriv f R,deriv g R)).mpr hboundary

end DefocusingNLS

end OAI
