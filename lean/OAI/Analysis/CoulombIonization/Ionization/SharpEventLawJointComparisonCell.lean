import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.FreshRetainedMassBarrier

namespace OAI

noncomputable section
namespace CoulombAtom

section
open MeasureTheory Set Metric
open scoped BigOperators ENNReal ContDiff
open CoulombAnalysis CoulombObservation

theorem sharp_eventLaw_joint_comparison_of_cell {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {N K : ℕ} (F G : fermionGraph N) (hG : ‖fermionGraphValue N G‖^2 = 1)
    (ell : Fin K → ℝ) (j : ℕ) {A : Set (Fin K × (Fin N × Fin 3) → ℝ)}
    (hinfo : MeasurableSet[observationInformation ell j] (physicalObservationEvent ell A))
    (hp : 0 < physicalObservationProbability F ell A)
    (hlaw : graphRawLaw G = (ENNReal.ofReal (physicalObservationProbability F ell A))⁻¹ •
      Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict
        (physicalObservationEvent ell A)))
    {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (hcell : 2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y)
    {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y) (hq : 0 < q)
    (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
    (hcollar : localCellRadius y ≤ b^2*
      localOffsetMass (max (corePriceExcess Z lam (graphFormVector G)) 0) y) :
    ∃ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y), ∃ ht : 0 ≤ t,
      radialPatchGapMean (graphFormVector G) y ht hb Z lam ≤
        corePriceExcess Z lam (graphFormVector G)+sharpPatchRemainder (localCellRadius y) b
          (localOffsetMass (max (corePriceExcess Z lam (graphFormVector G)) 0) y) ∧
      |Z/‖y‖-lam-(physicalObservationProbability F ell A)⁻¹*
        (∫ z in physicalObservationEvent ell A,
          tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket
            (originalDatum ell j z)) y ∂physicalObservationLaw (graphRawLaw F) K)-
        expectedRadialPatchCenter (graphFormVector G) y ht hb Z lam| ≤
        sharpPotentialRemainder (localCellRadius y) b
          (localOffsetMass (max (corePriceExcess Z lam (graphFormVector G)) 0) y)
          (max (corePriceExcess Z lam (graphFormVector G)) 0) q+
        sharpLocalPotentialBudget (localCellRadius y)
          (localOffsetMass (max (corePriceExcess Z lam (graphFormVector G)) 0) y)
          (2*masterWidth c₁ r₀ s y) := by
  have hψ := graphFormVector_admissible G hG
  have hm : formMass (graphFormVector G) = 1 := hψ.2.2.2.2.1
  obtain ⟨t,ht,ht0,hgap,hpot⟩ := sharp_joint_selected_patch hψ hy ha1 hb hba hZ hlam hq hqr hcollar
  refine ⟨t,ht,ht0,hgap,?_⟩
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    rw [←formRawLaw_graph]
    exact rawPotential_form_integrable (graphFormVector_sobolev F).sobolevVector y
  have he : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    rw [←formRawLaw_graph]
    exact formRawLaw_ae_no_poles (graphFormVector F) y
  have hn : t ≤ ‖y‖ := by
    have := ht.2
    unfold localCellRadius at this
    nlinarith [norm_nonneg y]
  have hcmp := original_master_radial_center_comparison (graphRawLaw F)
    hψ.sobolevFermion ell j y hi he hc hcL hr hs hs1 canonicalRealPacket_smooth
    canonicalRealPacket_compact canonicalRealPacket_normalized canonicalRealPacket_radial
    canonicalRealPacket_support hinfo hp (by rw [formRawLaw_graph]; exact hlaw)
    ht0 hb (by linarith [ht.1,localCellRadius_pos hy]) hn hZ hlam hq (by linarith [ht.1])
  have hraw := sharp_cell_local_potential hψ hy ha1 hZ hlam
    (by linarith [masterWidth_pos hc hr hs y] : 0 < 2*masterWidth c₁ r₀ s y)
    hcell
  simp only [hm,mul_one] at hcmp
  exact hcmp.trans (add_le_add hpot hraw)

end

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff
open CoulombAnalysis

theorem sharp_eventLaw_field_cap_of_cell {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {N K : ℕ} (F G : fermionGraph N) (hG : ‖fermionGraphValue N G‖^2 = 1)
    (ell : Fin K → ℝ) (j : ℕ) {A : Set (Fin K × (Fin N × Fin 3) → ℝ)}
    (hinfo : MeasurableSet[observationInformation ell j] (physicalObservationEvent ell A))
    (hp : 0 < physicalObservationProbability F ell A)
    (hlaw : graphRawLaw G = (ENNReal.ofReal (physicalObservationProbability F ell A))⁻¹ •
      Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict
        (physicalObservationEvent ell A)))
    {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (hcell : 2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y)
    {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y) (hq : 0 < q)
    (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
    (hcollar : localCellRadius y ≤ b^2*
      localOffsetMass (max (corePriceExcess Z lam (graphFormVector G)) 0) y) :
    Z/‖y‖-lam-(physicalObservationProbability F ell A)⁻¹*
      (∫ z in physicalObservationEvent ell A,
        tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket
          (originalDatum ell j z)) y ∂physicalObservationLaw (graphRawLaw F) K) ≤
      tfPatchCapConstant/(localCellRadius y)^4+
      (sharpPotentialRemainder (localCellRadius y) b
        (localOffsetMass (max (corePriceExcess Z lam (graphFormVector G)) 0) y)
        (max (corePriceExcess Z lam (graphFormVector G)) 0) q+
      sharpLocalPotentialBudget (localCellRadius y)
        (localOffsetMass (max (corePriceExcess Z lam (graphFormVector G)) 0) y)
        (2*masterWidth c₁ r₀ s y)) := by
  obtain ⟨t,ht,ht0,hgap,hcmp⟩ := sharp_eventLaw_joint_comparison_of_cell hZ hlam F G hG ell j
    hinfo hp hlaw hy ha1 hc hcL hr hs hs1 hcell hb hba hq hqr hqR hcollar
  have ha := localCellRadius_pos hy
  have hnorm : t ≤ ‖y‖ := by
    have := ht.2
    unfold localCellRadius at this
    nlinarith [norm_nonneg y]
  have hcap := expectedRadialPatchCenter_le (graphFormVector_sobolev G).sobolevVector
    y ht0 hb (by linarith [ht.1]) hnorm Z lam
  have hm : formMass (graphFormVector G) = 1 := (graphFormVector_admissible G hG).2.2.2.2.1
  rw [hm,mul_one] at hcap
  have hpw : (localCellRadius y)^4 ≤ (t-4*b)^4 := pow_le_pow_left₀ ha.le (by linarith [ht.1]) 4
  have hd := div_le_div_of_nonneg_left tfPatchCapConstant_pos.le (by positivity : 0 < (localCellRadius y)^4) hpw
  have hh := (le_abs_self _).trans hcmp
  linarith [hcap.trans hd]

section
open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget
attribute [local irreducible] radialPatchGapMean expectedRadialPatchCenter corePriceExcess

theorem TailTiltState.event_radial_comparison_of_cell {Z lam r : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (hstate : TailTiltState Z lam r K p₀ δ F)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (j : Fin (K+1)) {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1)
    (hcell : 2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y) {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y)
    (hq : 0 < q) (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
    (hcollar : localCellRadius y ≤ b^2*(1/(localCellRadius y)^3))
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j] A)
    (hprob : p₀ j ≤ ((physicalObservationLaw (graphRawLaw F) K) A).toReal) :
    ∃ G : fermionGraph N, ∃ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y), ∃ ht : 0 ≤ t,
      ‖fermionGraphValue N G‖^2 = 1 ∧
      graphRawLaw G = (ENNReal.ofReal (((physicalObservationLaw (graphRawLaw F) K) A).toReal))⁻¹ •
        Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict A) ∧
      radialPatchGapMean (graphFormVector G) y ht hb Z lam ≤
        dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ+
        sharpPatchRemainder (localCellRadius y) b
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y) ∧
      |Z/‖y‖-lam-(((physicalObservationLaw (graphRawLaw F) K) A).toReal)⁻¹*
        (∫ z in A, tfPotential (jointMasterPosterior (graphRawLaw F)
          (fun k : Fin K => dyadicObservationWidth r k) j c₁ r₀ s canonicalRealPacket
          (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z)) y
            ∂physicalObservationLaw (graphRawLaw F) K)-
        expectedRadialPatchCenter (graphFormVector G) y ht hb Z lam| ≤
        sharpPotentialRemainder (localCellRadius y) b
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) q+
        sharpLocalPotentialBudget (localCellRadius y)
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (2*masterWidth c₁ r₀ s y) := by
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  obtain ⟨B,hB,hBA⟩ := observation_event_tail_representation ell j hA
  let p := ((physicalObservationLaw (graphRawLaw F) K) A).toReal
  have hpB : physicalObservationProbability F ell B = p := by
    calc
      _ = ((physicalObservationLaw (graphRawLaw F) K) (physicalObservationEvent ell B)).toReal := by
        unfold physicalObservationProbability physicalObservationLaw
        rfl
      _ = p := by rw [hBA]
  have hp : 0 < p := (h₀ j).trans_le hprob
  refine (hstate.2.2 j A hA hprob).imp ?_
  intro G hG
  rcases hG with ⟨hGn,hlaw,hDE⟩
  have hcollar' : localCellRadius y ≤ b^2*localOffsetMass
      (max (corePriceExcess Z lam (graphFormVector G)) 0) y := by
    apply hcollar.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg b)
    unfold localOffsetMass
    linarith [le_max_left (1/(localCellRadius y)^3) 1,Real.sqrt_nonneg
      (max (corePriceExcess Z lam (graphFormVector G)) 0*localCellRadius y)]
  obtain ⟨t,ht,ht0,hgap,hpot⟩ := sharp_eventLaw_joint_comparison_of_cell hZ hlam F G hGn ell j
    (by rwa [hBA]) (by rwa [hpB]) (by rwa [hBA,hpB]) hy ha1 hc hcL hr₀ hs hs1 hcell
    hb hba hq hqr hqR hcollar'
  refine ⟨t,ht,ht0,hGn,hlaw,?_,?_⟩
  · apply hgap.trans
    exact add_le_add ((le_max_left _ _).trans hDE)
      (sharpPatchRemainder_mono (localCellRadius_pos hy) hb
        (le_trans zero_le_one (localOffsetMass_one_le _ y)) (localOffsetMass_mono hDE y))
  · rw [hpB,hBA] at hpot
    exact hpot.trans (sharp_combined_error_mono hy hb hq hDE
      (by linarith [masterWidth_pos hc hr₀ hs y]))

end

section
open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff NNReal
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget
attribute [local irreducible] radialPatchGapMean expectedRadialPatchCenter corePriceExcess

theorem TailTiltState.low_inverse_event_of_cell {Z lam r : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) (hr : 0 < r) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (hstate : TailTiltState Z lam r K p₀ δ F)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (j : Fin (K+1)) (k : Fin K) (hk : j.val ≤ k.val)
    {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1) (hcell : 2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y)
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
  obtain ⟨G,t,ht,ht0,hGn,hlaw,hgap,hpot⟩ := hstate.event_radial_comparison_of_cell hZ hlam h₀
    hc hcL hr₀ hs hs1 j hy ha1 hcell hb hba hq hqr hqR hcollar hA hn
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

end

section
open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff NNReal
open CoulombAnalysis CoulombObservation CoulombNeumann
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget
attribute [local irreducible] radialPatchGapMean expectedRadialPatchCenter corePriceExcess

theorem TailTiltState.high_inverse_event_of_cell {Z lam r : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) (hr : 0 < r) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (hstate : TailTiltState Z lam r K p₀ δ F)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (j : Fin (K+1)) (k : Fin K) (hk : j.val ≤ k.val)
    {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1) (hcell : 2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y)
    {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y)
    (hq : 0 < q) (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
    (hcollar : localCellRadius y ≤ b^2*(1/(localCellRadius y)^3))
    (hqk : 3*masterWidth c₁ r₀ s y ≤ (5*localCellRadius y-4*b)/12)
    {H eta m T Q θ : ℝ} (hH : 0 ≤ H) (heta : 0 < eta) (hm : 0 < m)
    (hosc : ∀ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y),
      tfPatchOscillationConstant/(t-4*b)*(3*masterWidth c₁ r₀ s y) ≤ 1/2)
    (hdensity : ∀ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y),
      max (freshHighThreshold y (t-4*b) H eta c₁ r₀ s)
        (canonicalMasterAmplitude*(masterWidth c₁ r₀ s y)⁻¹^3*m)+
      Q*((masterTestConstant canonicalRealPacket_smooth canonicalRealPacket_support:ℝ)*
        (masterWidth c₁ r₀ s y)⁻¹^4*Real.sqrt 3*(b+2*dyadicObservationWidth r k)) < T)
    (hsmall : ∀ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y),
      θ+(sharpPotentialRemainder (localCellRadius y) b
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) q+
        sharpLocalPotentialBudget (localCellRadius y)
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (2*masterWidth c₁ r₀ s y)) <
      H-(H/eta+2/m)*(dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ+
          sharpPatchRemainder (localCellRadius y) b
            (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y))-
        2*(tfPatchOscillationConstant/(t-4*b)*(3*masterWidth c₁ r₀ s y))*(t-4*b)⁻¹^4) :
    ((physicalObservationLaw (graphRawLaw F) K)
      {z | Z/‖y‖-lam-tfPotential (jointMasterPosterior (graphRawLaw F)
          (fun k : Fin K => dyadicObservationWidth r k) j c₁ r₀ s canonicalRealPacket
          (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z)) y ≤ θ ∧
        T ≤ jointMasterPosterior (graphRawLaw F) (fun k : Fin K => dyadicObservationWidth r k)
          j c₁ r₀ s canonicalRealPacket (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z) y ∧
        observedLocalCount (fun k : Fin K => dyadicObservationWidth r k) k y
          (2*masterWidth c₁ r₀ s y+Real.sqrt 3*(b+dyadicObservationWidth r k)) z ≤ Q}).toReal < p₀ j := by
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  let pot := fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
    tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket
      (originalDatum ell j z)) y
  let dens := fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
    jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket (originalDatum ell j z) y
  let A := {z | Z/‖y‖-lam-pot z ≤ θ ∧ T ≤ dens z ∧
    observedLocalCount ell k y (2*masterWidth c₁ r₀ s y+Real.sqrt 3*(b+ell k)) z ≤ Q}
  have hA : MeasurableSet[observationInformation ell j] A :=
    (measurableSet_le (measurable_const.sub
      (jointMasterPosterior_potential_measurable (graphRawLaw F) ell j y hc hr₀ hs canonicalRealPacket_smooth.continuous)) measurable_const).inter
      ((measurableSet_le measurable_const (jointMasterPosterior_value_measurable (graphRawLaw F) ell j y hc hr₀ hs)).inter
        (measurableSet_le (observedLocalCount_information_measurable ell k hk y _) measurable_const))
  change ((physicalObservationLaw (graphRawLaw F) K) A).toReal < p₀ j
  by_contra! hn
  have hp := (h₀ j).trans_le hn
  obtain ⟨G,t,ht,ht0,hGn,hlaw,hgap,hpot⟩ := hstate.event_radial_comparison_of_cell hZ hlam h₀
    hc hcL hr₀ hs hs1 j hy ha1 hcell hb hba hq hqr hqR hcollar hA hn
  have hψ := graphFormVector_admissible G hGn
  have hmass : formMass (graphFormVector G) = 1 := hψ.2.2.2.2.1
  have ha := localCellRadius_pos hy
  have hw := masterWidth_pos hc hr₀ hs y
  have hnuc : t ≤ ‖y‖ := by
    have hh := ht.2
    unfold localCellRadius at hh
    nlinarith [norm_nonneg y]
  have htb : 7*b < t := by linarith [ht.1]
  have hkr : 2*masterWidth c₁ r₀ s y < t-7*b := by linarith [ht.1]
  have hhigh := event_fresh_high_test_support F G ell (fun k => (dyadicObservationWidth_pos hr k).le)
    k hk y ht0 hb hkr
    (masterKernel_test_lipschitz canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
    (masterKernel_test_support canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
    ((observationInformation_le ell j) A hA) hlaw
    (max (freshHighThreshold y (t-4*b) H eta c₁ r₀ s)
      (canonicalMasterAmplitude*(masterWidth c₁ r₀ s y)⁻¹^3*m)) Q
    (by
      filter_upwards [jointMasterPosterior_eq_scalar (graphRawLaw F) ell j hc hcL hr₀ hs hs1
        canonicalRealPacket_smooth canonicalRealPacket_support y] with z hz
      intro hzA
      refine ⟨?_,hzA.2.2⟩
      have hden := hzA.2.1
      dsimp only [dens] at hden
      rw [←hz] at hden
      exact (hdensity t ht).trans_le hden)
  have hcount : ∀ c : Fin N → Fin 2, ∀ spin : Spins (cutOutNumber c), ∀ᵐ u,
      formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht0 hb)
        (coreFirstRadialCut_partition y ht0 hb) (graphFormVector G) c) spin u) ≠ 0 →
      m ≤ ∫ z in ball (0 : Space) (3*masterWidth c₁ r₀ s y),
        retainedPatchLp hb (radialPatchRetention N y t b c spin u) u y (t-4*b) z ∂ballMeasure (t-4*b) := by
    intro c spin
    filter_upwards [hhigh c spin] with u hu
    intro hmu
    have htest := compact_test_le_mass
      (retainedPatchLp hb (radialPatchRetention N y t b c spin u) u y (t-4*b))
      (retainedPatchLp_nonneg hb _ _ _ _)
      (masterCenteredKernel_lipschitz canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
      (masterCenteredKernel_support canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
      (by linarith : 2*masterWidth c₁ r₀ s y < 3*masterWidth c₁ r₀ s y)
      (canonicalMasterAmplitude_bound hc hcL hr₀ hs hs1 y)
    have hh := ((le_max_right _ _).trans_lt (hu hmu)).le.trans htest
    exact (mul_le_mul_iff_of_pos_left (mul_pos canonicalMasterAmplitude_pos (pow_pos (inv_pos.mpr hw) 3))).mp hh
  have hcmean := radial_high_mean_expected_center hψ.sobolevFermion y ht0 hb htb hnuc hZ hlam
    (masterCenteredKernel_lipschitz canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
    (fun x => masterKernel_nonneg c₁ r₀ s canonicalRealPacket (y+x) y)
    (by linarith : 0 < 3*masterWidth c₁ r₀ s y)
    ((masterCenteredKernel_support canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y).trans
      (closedBall_subset_closedBall (by linarith)))
    (by linarith [ht.1] : 3*masterWidth c₁ r₀ s y ≤ (t-4*b)/12) (hosc t ht) hH heta hm hcount
    (by
      intro c spin
      filter_upwards [hhigh c spin] with u hu
      intro hmu
      exact (le_max_left _ _).trans_lt (hu hmu))
  rw [hmass,mul_one,mul_one] at hcmean
  have hcoef : 0 ≤ H/eta+2/m := by positivity
  have hcenter := (sub_le_sub_right (sub_le_sub_left (mul_le_mul_of_nonneg_left hgap hcoef) H)
    (2*(tfPatchOscillationConstant/(t-4*b)*(3*masterWidth c₁ r₀ s y))*(t-4*b)⁻¹^4)).trans hcmean
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    simpa only [formRawLaw_graph] using rawPotential_form_integrable (graphFormVector_sobolev F).sobolevVector y
  have he : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    simpa only [formRawLaw_graph] using formRawLaw_ae_no_poles (graphFormVector F) y
  have hPi := jointMasterPosterior_potential_integrable (graphRawLaw F) ell j y hi he hc hr₀ hs
    canonicalRealPacket_smooth canonicalRealPacket_compact canonicalRealPacket_normalized
    canonicalRealPacket_radial canonicalRealPacket_support
  have hupper := threshold_event_mean_le (physicalObservationLaw (graphRawLaw F) K)
    ((integrable_const (Z/‖y‖-lam)).sub hPi) ((observationInformation_le ell j) A hA)
    (fun z hz => hz.1) hp
  simp only [Pi.sub_apply] at hupper
  rw [normalized_setIntegral_const_sub _ A hPi hp] at hupper
  have hplower := (abs_le.mp hpot).1
  have hstrict := hsmall t ht
  linarith

end

open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget

end CoulombAtom
end

end OAI
