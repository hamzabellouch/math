import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSecondCorePower
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeightExt
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakOperator

namespace OAI

/-! The actual matched-profile limiting pencil satisfies the regular core interface conditions. -/

open Set Filter Topology
open scoped SchwartzMap
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedFreeMass_core (z : ProfileMatchingBall) (r : ℝ)
    (hr : r ≤ radialShootingR (profileMatchingParameter z)) :
    radialMatchedFreeMassFunction z r=1 := by
  have hb := (radialShooting_geometry (profileMatchingParameter z)).2.2.2.1
  simp only [radialMatchedFreeMassFunction,radialMatchedFreeProfile,
    ite_eq_left (hr.trans hb),ite_eq_left hr,norm_one,one_pow]

theorem radialMatchedFreeMass_pos (z : ProfileMatchingBall) (r : ℝ) (hr : 0 ≤ r) :
    0 < radialMatchedFreeMassFunction z r :=
  sq_pos_of_pos (norm_pos_iff.mpr
    (radialMatchedFreeProfile_ne_zero (fun n => n) strictMono_id (fun _ => z) z
      tendsto_const_nhds r hr))

theorem radialMatchedLimit_kernel_core (ell : ℕ) (z : ProfileMatchingBall)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (s : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z)))
    (hmass : s.limitWeight.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) (v : SpectralRadialObservationSpace R)
    (hv : s.limitPencil ell
      (lt_of_lt_of_le (by norm_num) (radialShooting_geometry (profileMatchingParameter z)).2.1)
      hLR (radialMatchedLimitWeakOperator ell z hc R
        ((lt_of_lt_of_le (by norm_num) (radialShooting_geometry (profileMatchingParameter z)).2.1).trans hLR)
        ζ B) v=v) :
    let hR : 0 < R :=
      (lt_of_lt_of_le (by norm_num) (radialShooting_geometry (profileMatchingParameter z)).2.1).trans hLR
    ∃ u : SpectralHarmonicPair ell R,
      spectralHarmonicObservation ell R hR u=v ∧
      spectralHarmonicRepresentative ell R hR u.fst (radialShootingR (profileMatchingParameter z))=0 ∧
      ContinuousOn (deriv (spectralHarmonicRepresentative ell R hR u.snd)) (Ioo 0 R) ∧
      ∃ C : ℂ,
        (∀ x ∈ Ioc 0 (radialShootingR (profileMatchingParameter z)),
          spectralHarmonicRepresentative ell R hR u.snd x=C*(x : ℂ)^ell) ∧
        deriv (spectralHarmonicRepresentative ell R hR u.snd)
          (radialShootingR (profileMatchingParameter z))=
          (ell : ℂ)*spectralHarmonicRepresentative ell R hR u.snd
            (radialShootingR (profileMatchingParameter z))/
            (radialShootingR (profileMatchingParameter z) : ℂ) := by
  dsimp only
  let L := radialShootingR (profileMatchingParameter z)
  have hL : 0 < L := lt_of_lt_of_le (by norm_num)
    (radialShooting_geometry (profileMatchingParameter z)).2.1
  let hR := hL.trans hLR
  let a := spectralContinuousCoefficient R (radialMatchedFreeTransportFunction z)
    (continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc)))
  have hQ := spectralRadialWeightMultiplier_eq_of_density R s.limitWeight
    (spectralContinuousCoefficient R (radialMatchedFreeMassFunction z) hc) hmass
  obtain ⟨u,hu,hobs,hweak⟩ := (s.limitPencil_complex_variational ell hL hLR _ v).mp hv
  have he : ∀ f : 𝓢(ℝ,ℂ),
      spectralHarmonicPairComplexForm ell R s.limitWeight u (spectralSecondTest ell R f)=
      inner ℂ (spectralLowerOrderOperator ell R hR (spectralRadialWeightMultiplier R s.limitWeight)
        (spectralRadialWeightMultiplier R a) 6 ζ B (spectralHarmonicObservation ell R hR u))
        (spectralSecondTest ell R f) := by
    intro f
    have ht := hweak ⟨spectralSecondTest ell R f,spectralSecondTest_core ell R L f⟩
    simpa only [hobs,hQ,radialMatchedLimitWeakOperator,a] using ht
  have hw : ContinuousOn s.limitWeight.density (Ioo 0 R) := by rw [hmass]; exact hc.continuousOn
  have ha : ContinuousOn a.density (Ioo 0 R) :=
    (continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc))).continuousOn
  have hp (x : ℝ) (hx : x ∈ Ioo 0 R) : 0 < s.limitWeight.density x := by
    rw [hmass]
    exact radialMatchedFreeMass_pos z x hx.1.le
  obtain ⟨C,hC,hderiv⟩ := spectralSecond_core_power ell R L hR hL hLR s.limitWeight a u
    6 ζ B hu hw ha hp (fun x hx => by rw [hmass]; exact radialMatchedFreeMass_core z x hx.2) he
  exact ⟨u,hobs,spectralHarmonicCore_representative_zero ell R L hR hLR.le u hu L ⟨hL,le_rfl⟩,
    (spectralSecond_classical ell R hR s.limitWeight a u 6 ζ B hw ha hp he).2.1,C,hC,hderiv⟩

end DefocusingNLS

end OAI
