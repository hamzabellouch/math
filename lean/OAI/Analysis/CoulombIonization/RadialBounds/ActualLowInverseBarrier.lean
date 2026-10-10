import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.RadialMeanCenterBarrier
import OAI.Analysis.CoulombIonization.Localization.PosteriorFreshTestBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff NNReal

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget
attribute [local irreducible] radialPatchGapMean expectedRadialPatchCenter corePriceExcess

 def freshLowThreshold (y : Space) (R H eta : ℝ) (c₁ r₀ s : ℝ) : ℝ :=
  (max (H-(tfPatchOscillationConstant/R*(2*masterWidth c₁ r₀ s y))*R⁻¹^4) 0/
    ((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
    (∫ x, masterCenteredKernel c₁ r₀ s canonicalRealPacket y x ∂ballMeasure R)-
  Real.sqrt ((16*(2*masterWidth c₁ r₀ s y)^3*
    ((masterTestConstant canonicalRealPacket_smooth canonicalRealPacket_support:ℝ)*
      (masterWidth c₁ r₀ s y)⁻¹^4)^2)*eta)

lemma jointMasterPosterior_value_measurable {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) :
    Measurable (fun z : OriginalDatum N K ell j =>
      jointMasterPosterior μ ell j c₁ r₀ s canonicalRealPacket z y) :=
  (jointMasterPosterior_measurable μ ell j hc hr hs canonicalRealPacket_smooth.continuous).comp
    (measurable_id.prodMk measurable_const)

 theorem TailTiltState.low_inverse_event {Z lam r : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) (hr : 0 < r) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (hstate : TailTiltState Z lam r K p₀ δ F)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (j : Fin (K+1)) (k : Fin K) (hk : j.val ≤ k.val)
    {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1) (hry : r₀ ≤ ‖y‖)
    {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y)
    (hq : 0 < q) (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
    (hcollar : localCellRadius y ≤ b^2*(1/(localCellRadius y)^3))
    (hqk : 2*masterWidth c₁ r₀ s y ≤ (5*localCellRadius y-4*b)/12)
    {H eta T Q θ : ℝ} (hH : 0 ≤ H) (heta : 0 < eta)
    (hdensity : ∀ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y),
      T+Q*((masterTestConstant canonicalRealPacket_smooth canonicalRealPacket_support:ℝ)*
        (masterWidth c₁ r₀ s y)⁻¹^4*Real.sqrt 3*(b+2*dyadicObservationWidth r k)) <
      freshLowThreshold y (t-4*b) H eta c₁ r₀ s)
    (hsmall : ∀ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y),
      H+((tfPatchCapConstant/(t-4*b)^4)/eta)*
        (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ+
          sharpPatchRemainder (localCellRadius y) b
            (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y))+
        (sharpPotentialRemainder (localCellRadius y) b
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) q+
        sharpLocalPotentialBudget (localCellRadius y)
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (2*masterWidth c₁ r₀ s y)) < θ) :
    ((physicalObservationLaw (graphRawLaw F) K)
      {z | θ ≤ Z/‖y‖-lam-tfPotential (jointMasterPosterior (graphRawLaw F)
          (fun k : Fin K => dyadicObservationWidth r k) j c₁ r₀ s canonicalRealPacket
          (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z)) y ∧
        jointMasterPosterior (graphRawLaw F) (fun k : Fin K => dyadicObservationWidth r k)
          j c₁ r₀ s canonicalRealPacket (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z) y ≤ T ∧
        observedLocalCount (fun k : Fin K => dyadicObservationWidth r k) k y
          (2*masterWidth c₁ r₀ s y+Real.sqrt 3*(b+dyadicObservationWidth r k)) z ≤ Q}).toReal < p₀ j := by
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  let pot := fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
    tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket
      (originalDatum ell j z)) y
  let dens := fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
    jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket (originalDatum ell j z) y
  let A := {z | θ ≤ Z/‖y‖-lam-pot z ∧ dens z ≤ T ∧
    observedLocalCount ell k y (2*masterWidth c₁ r₀ s y+Real.sqrt 3*(b+ell k)) z ≤ Q}
  have hA : MeasurableSet[observationInformation ell j] A :=
    (measurableSet_le measurable_const (measurable_const.sub
      (jointMasterPosterior_potential_measurable (graphRawLaw F) ell j y hc hr₀ hs canonicalRealPacket_smooth.continuous))).inter
      ((measurableSet_le (jointMasterPosterior_value_measurable (graphRawLaw F) ell j y hc hr₀ hs) measurable_const).inter
        (measurableSet_le (observedLocalCount_information_measurable ell k hk y _) measurable_const))
  change ((physicalObservationLaw (graphRawLaw F) K) A).toReal < p₀ j
  by_contra! hn
  have hp := (h₀ j).trans_le hn
  obtain ⟨G,t,ht,ht0,hGn,hlaw,hgap,hpot⟩ := hstate.event_radial_comparison hZ hlam h₀
    hc hcL hr₀ hs hs1 j hy ha1 hry hb hba hq hqr hqR hcollar hA hn
  have hψ := graphFormVector_admissible G hGn
  have hm : formMass (graphFormVector G) = 1 := hψ.2.2.2.2.1
  have ha := localCellRadius_pos hy
  have hnuc : t ≤ ‖y‖ := by
    have hh := ht.2
    unfold localCellRadius at hh
    nlinarith [norm_nonneg y]
  have htb : 7*b < t := by linarith [ht.1]
  have hkr : 2*masterWidth c₁ r₀ s y < t-7*b := by linarith [ht.1]
  have hlow := event_fresh_low_test_support F G ell (fun k => (dyadicObservationWidth_pos hr k).le)
    k hk y ht0 hb hkr
    (masterKernel_test_lipschitz canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
    (masterKernel_test_support canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
    ((observationInformation_le ell j) A hA) hlaw (freshLowThreshold y (t-4*b) H eta c₁ r₀ s) Q
    (by
      filter_upwards [jointMasterPosterior_eq_scalar (graphRawLaw F) ell j hc hcL hr₀ hs hs1
        canonicalRealPacket_smooth canonicalRealPacket_support y] with z hz
      intro hzA
      refine ⟨?_,hzA.2.2⟩
      have hden := hzA.2.1
      dsimp only [dens] at hden
      rw [←hz] at hden
      exact (add_le_add hden le_rfl).trans_lt (hdensity t ht))
  have hcmean := radial_low_mean_expected_center hψ.sobolevFermion y ht0 hb htb hnuc hZ hlam
    (masterCenteredKernel_lipschitz canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
    (fun x => masterKernel_nonneg c₁ r₀ s canonicalRealPacket (y+x) y)
    (by linarith [masterWidth_pos hc hr₀ hs y])
    (masterCenteredKernel_support canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
    (by linarith [ht.1] : 2*masterWidth c₁ r₀ s y ≤ (t-4*b)/12) hH heta
    (by
      intro c spin
      filter_upwards [hlow c spin] with u hu
      intro hmu
      have hh := hu hmu
      dsimp only [freshRadialTest,freshLowThreshold] at hh
      exact lt_sub_iff_add_lt.mp hh)
  rw [hm,mul_one] at hcmean
  have hcap : 0 ≤ (tfPatchCapConstant/(t-4*b)^4)/eta := by
    exact div_nonneg (div_nonneg tfPatchCapConstant_pos.le (pow_nonneg (by linarith : 0 ≤ t-4*b) _)) heta.le
  have hcenter := hcmean.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hgap hcap))
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    simpa only [formRawLaw_graph] using rawPotential_form_integrable (graphFormVector_sobolev F).sobolevVector y
  have he : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    simpa only [formRawLaw_graph] using formRawLaw_ae_no_poles (graphFormVector F) y
  have hPi := jointMasterPosterior_potential_integrable (graphRawLaw F) ell j y hi he hc hr₀ hs
    canonicalRealPacket_smooth canonicalRealPacket_compact canonicalRealPacket_normalized
    canonicalRealPacket_radial canonicalRealPacket_support
  have hlower := threshold_event_mean_ge (physicalObservationLaw (graphRawLaw F) K)
    ((integrable_const (Z/‖y‖-lam)).sub hPi) ((observationInformation_le ell j) A hA)
    (fun z hz => hz.1) hp
  simp only [Pi.sub_apply] at hlower
  rw [normalized_setIntegral_const_sub _ A hPi hp] at hlower
  have hpupper := (abs_le.mp hpot).2
  have hstrict := hsmall t ht
  linarith

end CoulombAtom

end

end OAI
