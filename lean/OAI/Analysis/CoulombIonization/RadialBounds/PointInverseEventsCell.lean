import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.OwnProbabilityRareCapBarrier
import OAI.Analysis.CoulombIonization.Ionization.SharpEventLawJointComparisonCell

namespace OAI

noncomputable section
namespace CoulombAtom
section
open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget

theorem TailTiltState.point_inverse_events_of_cell {Z lam r : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) (hr : 0 < r) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (hstate : TailTiltState Z lam r K p₀ δ F)
    {c₁ r₀ s h xi : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (hxi : 0 < xi) (hxih : xi < 2*h)
    (j : Fin (K+1)) (k : Fin K) (hk : j.val ≤ k.val)
    {y : Space} (hy : y ≠ 0)
    (hgeom : InverseFiniteGeometry c₁ r₀ s (dyadicObservationWidth r k) y)
    (hlow : LowInverseNumerics c₁ r₀ s (dyadicObservationWidth r k)
      (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) h xi quantumInverseCountConstant y)
    (hhigh : HighInverseNumerics c₁ r₀ s (dyadicObservationWidth r k)
      (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) h xi quantumInverseCountConstant y)
    (hcount : universalCellCountConstant*
      (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)^2 <
      (quantumInverseCountConstant/(localCellRadius y)^3)^2) :
    (physicalObservationLaw (graphRawLaw F) K).real
      {z | (h+xi)/(localCellRadius y)^4 ≤ originalQueryField F Z lam r j c₁ r₀ s z y ∧
        originalQueryDensity F r j c₁ r₀ s z y ≤ localTFResponse h/(localCellRadius y)^6} < 2*p₀ j ∧
    (physicalObservationLaw (graphRawLaw F) K).real
      {z | originalQueryField F Z lam r j c₁ r₀ s z y ≤ (h-xi)/(localCellRadius y)^4 ∧
        localTFResponse h/(localCellRadius y)^6 ≤ originalQueryDensity F r j c₁ r₀ s z y} < 2*p₀ j := by
  have ha := localCellRadius_pos hy
  have hcell : 2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y := by
    linarith [hgeom.master_fit, hgeom.cut_pos]
  have hw := masterWidth_pos hc hr₀ hs y
  have hHlo : 0 ≤ (h+xi/2)/(localCellRadius y)^4 := div_nonneg (by linarith) (by positivity)
  have hHhi : 0 ≤ (h-xi/2)/(localCellRadius y)^4 := div_nonneg (by linarith) (by positivity)
  have heta : 0 < (localCellRadius y)^(-7+(1/100:ℝ)) := Real.rpow_pos_of_pos ha _
  have hm : 0 < (localCellRadius y)^(-3+(1/100:ℝ)) := Real.rpow_pos_of_pos ha _
  have hlo := hstate.low_inverse_event_of_cell hZ hlam hr h₀ hc hcL hr₀ hs hs1 j k hk hy
    hgeom.radius_le hcell hgeom.cut_pos hgeom.cut_le hgeom.probe_pos hgeom.probe_fit
    hgeom.probe_margin hgeom.collar (by linarith [hgeom.master_fit]) hHlo heta
    (fun t ht => (hlow t ht).1) (fun t ht => (hlow t ht).2)
  have hhi := hstate.high_inverse_event_of_cell hZ hlam hr h₀ hc hcL hr₀ hs hs1 j k hk hy
    hgeom.radius_le hcell hgeom.cut_pos hgeom.cut_le hgeom.probe_pos hgeom.probe_fit
    hgeom.probe_margin hgeom.collar hgeom.master_fit hHhi heta hm
    (fun t ht => (hhigh t ht).1) (fun t ht => (hhigh t ht).2.1) (fun t ht => (hhigh t ht).2.2)
  have hcnt := hstate.local_count_failure hZ hlam hr j k hk hy
    (2*masterWidth c₁ r₀ s y+Real.sqrt 3*((localCellRadius y)^(6/5:ℝ)+dyadicObservationWidth r k))
    (quantumInverseCountConstant/(localCellRadius y)^3)
    (div_nonneg quantumInverseCountConstant_pos.le (by positivity))
    (by linarith only [hgeom.count_fit]) hcount
  constructor
  · apply measureReal_remove_cutoff (physicalObservationLaw (graphRawLaw F) K) (hQ := hcnt)
    unfold originalQueryField originalQueryDensity
    simpa only [mem_ofPred_eq,and_assoc,Measure.real] using hlo
  · apply measureReal_remove_cutoff (physicalObservationLaw (graphRawLaw F) K) (hQ := hcnt)
    unfold originalQueryField originalQueryDensity
    simpa only [mem_ofPred_eq,and_assoc,Measure.real] using hhi

end

section
open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

theorem TailTiltState.posterior_cap_of_cell {Z lam r : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (hstate : TailTiltState Z lam r K p₀ δ F)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) :
      ∀ (j : Fin (K+1)) (y : Space) (_hy : y ≠ 0) (_ha1 : localCellRadius y ≤ 1)
        (_hcell : 2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y) (b q θ : ℝ) (_hb : 0 < b) (_hba : 2*b ≤ localCellRadius y)
        (_hq : 0 < q) (_hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
        (_hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
        (_hcollar : localCellRadius y ≤ b^2*(1/(localCellRadius y)^3)),
      tfPatchCapConstant/(localCellRadius y)^4+
        (sharpPotentialRemainder (localCellRadius y) b
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) q+
        sharpLocalPotentialBudget (localCellRadius y)
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (2*masterWidth c₁ r₀ s y)) < θ →
      ((physicalObservationLaw (graphRawLaw F) K)
        {z | θ < Z/‖y‖-lam-tfPotential (jointMasterPosterior (graphRawLaw F)
          (fun k : Fin K => dyadicObservationWidth r k) j c₁ r₀ s canonicalRealPacket
            (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z)) y}).toReal < p₀ j := by
  intro j y hy ha1 hcell b q θ hb hba hq hqr hqR hcollar hsmall
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  let P := fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
    tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket
      (originalDatum ell j z)) y
  let A := {z | θ < Z/‖y‖-lam-P z}
  have hA : MeasurableSet[observationInformation ell j] A :=
    measurableSet_lt measurable_const (measurable_const.sub
      (jointMasterPosterior_potential_measurable (graphRawLaw F) ell j y hc hr₀ hs canonicalRealPacket_smooth.continuous))
  obtain ⟨B,hB,hBA⟩ := observation_event_tail_representation ell j hA
  let p := ((physicalObservationLaw (graphRawLaw F) K) A).toReal
  have hpB : physicalObservationProbability F ell B = p := by
    change ((physicalObservationLaw (graphRawLaw F) K) (physicalObservationEvent ell B)).toReal = p
    rw [hBA]
  change p < p₀ j
  by_contra! hn
  have hp : 0 < p := (h₀ j).trans_le hn
  obtain ⟨G,hGn,hlaw,hDE⟩ := hstate.2.2 j A hA hn
  rw [←hBA] at hlaw
  have hcollar' : localCellRadius y ≤ b^2*localOffsetMass
      (max (corePriceExcess Z lam (graphFormVector G)) 0) y := by
    apply hcollar.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg b)
    unfold localOffsetMass
    linarith [le_max_left (1/(localCellRadius y)^3) 1,Real.sqrt_nonneg
      (max (corePriceExcess Z lam (graphFormVector G)) 0*localCellRadius y)]
  have hupper := sharp_eventLaw_field_cap_of_cell hZ hlam F G hGn ell j
    (by rwa [hBA]) (by rwa [hpB]) hlaw hy ha1 hc hcL hr₀ hs hs1 hcell hb hba hq hqr hqR hcollar'
  have herror := sharp_combined_error_mono hy hb hq hDE
    (by linarith [masterWidth_pos hc hr₀ hs y] : 0 ≤ 2*masterWidth c₁ r₀ s y)
  rw [hpB,hBA] at hupper
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    simpa only [formRawLaw_graph] using rawPotential_form_integrable (graphFormVector_sobolev F).sobolevVector y
  have he : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    simpa only [formRawLaw_graph] using formRawLaw_ae_no_poles (graphFormVector F) y
  have hPi : Integrable P (physicalObservationLaw (graphRawLaw F) K) :=
    jointMasterPosterior_potential_integrable (graphRawLaw F) ell j y hi he hc hr₀ hs
      canonicalRealPacket_smooth canonicalRealPacket_compact canonicalRealPacket_normalized
        canonicalRealPacket_radial canonicalRealPacket_support
  have hlower := threshold_event_mean_ge (physicalObservationLaw (graphRawLaw F) K)
    ((integrable_const (Z/‖y‖-lam)).sub hPi) ((observationInformation_le ell j) A hA)
    (fun z hz => hz.le) hp
  simp only [Pi.sub_apply] at hlower
  rw [normalized_setIntegral_const_sub _ A hPi hp] at hlower
  exact (not_le_of_gt (lt_of_le_of_lt (hupper.trans (add_le_add le_rfl herror)) hsmall)) hlower

end

section
open MeasureTheory Filter Set
open scoped BigOperators ENNReal
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

theorem OwnProbabilityTailTiltState.event_integral_cap_of_cell {Z lam r : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (hF : OwnProbabilityTailTiltState Z lam r K p₀ δ F)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (j : Fin (K+1))
    (A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)))
    (hA : MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j] A)
    (hp : p₀ j ≤ (physicalObservationLaw (graphRawLaw F) K).real A)
    {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1) (hcell : 2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y)
    {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y) (hq : 0 < q)
    (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
    (hcollar : localCellRadius y ≤ b^2*(1/(localCellRadius y)^3)) :
    (∫ z in A, originalQueryField F Z lam r j c₁ r₀ s z y
      ∂physicalObservationLaw (graphRawLaw F) K) ≤
    (physicalObservationLaw (graphRawLaw F) K).real A*
      originalFieldCapBudget ((2:ℝ)^j.val*r)
        ((physicalObservationLaw (graphRawLaw F) K).real A) δ c₁ r₀ s y b q := by
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  let p := (physicalObservationLaw (graphRawLaw F) K).real A
  have hpp : 0 < p := (h₀ j).trans_le hp
  obtain ⟨B,hB,hBA⟩ := observation_event_tail_representation ell j hA
  have hpB : physicalObservationProbability F ell B = p := by
    change ((physicalObservationLaw (graphRawLaw F) K) (physicalObservationEvent ell B)).toReal = p
    rw [hBA]
    rfl
  obtain ⟨G,hGn,hlaw,hDE⟩ := hF.2.2 j A hA hp
  rw [←hBA] at hlaw
  have hcollar' : localCellRadius y ≤ b^2*localOffsetMass
      (max (corePriceExcess Z lam (graphFormVector G)) 0) y := by
    apply hcollar.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg b)
    unfold localOffsetMass
    linarith [le_max_left (1/(localCellRadius y)^3) 1,Real.sqrt_nonneg
      (max (corePriceExcess Z lam (graphFormVector G)) 0*localCellRadius y)]
  have hu := sharp_eventLaw_field_cap_of_cell hZ hlam F G hGn ell j
    (by rwa [hBA]) (by rwa [hpB]) hlaw hy ha1 hc hcL hr₀ hs hs1 hcell hb hba hq hqr hqR hcollar'
  have he := sharp_combined_error_mono hy hb hq hDE
    (by linarith [masterWidth_pos hc hr₀ hs y] : 0 ≤ 2*masterWidth c₁ r₀ s y)
  rw [hpB,hBA] at hu
  have hh := hu.trans (add_le_add le_rfl he)
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    simpa only [formRawLaw_graph] using rawPotential_form_integrable
      (graphFormVector_sobolev F).sobolevVector y
  have hnp : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    simpa only [formRawLaw_graph] using formRawLaw_ae_no_poles (graphFormVector F) y
  have hPi := jointMasterPosterior_potential_integrable (graphRawLaw F) ell j y hi hnp hc hr₀ hs
    canonicalRealPacket_smooth canonicalRealPacket_compact canonicalRealPacket_normalized
    canonicalRealPacket_radial canonicalRealPacket_support
  dsimp only [p,Measure.real] at hh
  rw [←normalized_setIntegral_const_sub _ A hPi hpp] at hh
  change p⁻¹*(∫ z in A, originalQueryField F Z lam r j c₁ r₀ s z y
    ∂physicalObservationLaw (graphRawLaw F) K) ≤
      originalFieldCapBudget ((2:ℝ)^j.val*r) p δ c₁ r₀ s y b q at hh
  have hmul := mul_le_mul_of_nonneg_left hh hpp.le
  simpa only [←mul_assoc,mul_inv_cancel₀ hpp.ne',one_mul] using hmul

end

open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

theorem OwnProbabilityTailTiltState.rare_cap_event_of_cell {Z lam r : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hr : 0 < r) {N K : ℕ} {F : fermionGraph N}
    {δ c₁ r₀ s : ℝ}
    (hF : OwnProbabilityTailTiltState Z lam r K
      (fun j => tinyProbabilityFloor Z ((2:ℝ)^j.val*r)) δ F)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (j : Fin (K+1)) {y : Space} (hy : y ≠ 0)
    (hu1 : (2:ℝ)^j.val*r ≤ 1)
    (hgeom : InverseFiniteGeometry c₁ r₀ s (((2:ℝ)^j.val*r)^(101/100:ℝ)) y)
    (hcap : originalFieldCapBudget ((2:ℝ)^j.val*r) (((2:ℝ)^j.val*r)^80) δ c₁ r₀ s y
        ((localCellRadius y)^(6/5:ℝ)) (localCellRadius y*(localCellRadius y)^masterExponent) <
        (tfPatchCapConstant+2)/(localCellRadius y)^4) :
    (physicalObservationLaw (graphRawLaw F) K).real
      {z | (tfPatchCapConstant+2)/(localCellRadius y)^4 <
        originalQueryField F Z lam r j c₁ r₀ s z y} < ((2:ℝ)^j.val*r)^80 := by
  have hcell : 2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y := by
    linarith [hgeom.master_fit,hgeom.cut_pos,localCellRadius_pos hy]
  let p₁ : Fin (K+1) → ℝ := fun k => min 1 (((2:ℝ)^k.val*r)^80)
  have h₁ : ∀ k, 0 < p₁ k := by intro k; dsimp [p₁]; positivity
  have hT := hF.to_tailTiltState hr h₁
    (fun _ => tinyProbabilityFloor_le_eighty hZ (by positivity))
  have hu : 0 < (2:ℝ)^j.val*r := by positivity
  have hj : p₁ j = ((2:ℝ)^j.val*r)^80 := min_eq_right (pow_le_one₀ hu.le hu1)
  have hh := hT.posterior_cap_of_cell hZ hlam h₁ hc hcL hr₀ hs hs1 j y hy hgeom.radius_le hcell
    ((localCellRadius y)^(6/5:ℝ)) (localCellRadius y*(localCellRadius y)^masterExponent)
    ((tfPatchCapConstant+2)/(localCellRadius y)^4)
    hgeom.cut_pos hgeom.cut_le hgeom.probe_pos hgeom.probe_fit hgeom.probe_margin hgeom.collar
    (by rw [hj]; exact hcap)
  unfold originalQueryField originalQueryDensity
  simpa only [hj,Measure.real] using hh

end CoulombAtom

end

end OAI
