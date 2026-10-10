import Mathlib
import OAI.Analysis.CoulombIonization.Localization.ActualPointInverseBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.OwnProbabilityTailTiltBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

 def originalFieldCapBudget (u p δ c₁ r₀ s : ℝ) (y : Space) (b q : ℝ) : ℝ :=
  tfPatchCapConstant/(localCellRadius y)^4+
    (sharpPotentialRemainder (localCellRadius y) b
      (localOffsetMass (dyadicUniformEventBudget u p δ) y)
      (dyadicUniformEventBudget u p δ) q+
    sharpLocalPotentialBudget (localCellRadius y)
      (localOffsetMass (dyadicUniformEventBudget u p δ) y)
      (2*masterWidth c₁ r₀ s y))

lemma originalQueryField_integrable {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s) (y : Space) :
    Integrable (fun z => originalQueryField F Z lam r j c₁ r₀ s z y)
      (physicalObservationLaw (graphRawLaw F) K) := by
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    simpa only [formRawLaw_graph] using rawPotential_form_integrable
      (graphFormVector_sobolev F).sobolevVector y
  have he : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    simpa only [formRawLaw_graph] using formRawLaw_ae_no_poles (graphFormVector F) y
  exact (integrable_const (Z/‖y‖-lam)).sub
    (jointMasterPosterior_potential_integrable (graphRawLaw F)
      (fun k : Fin K => dyadicObservationWidth r k) j y hi he hc hr₀ hs
      canonicalRealPacket_smooth canonicalRealPacket_compact canonicalRealPacket_normalized
      canonicalRealPacket_radial canonicalRealPacket_support)

lemma originalQueryField_le_nuclear {N K : ℕ} (F : fermionGraph N)
    (Z r : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) (j : ℕ) (c₁ r₀ s : ℝ)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) (y : Space) :
    originalQueryField F Z lam r j c₁ r₀ s z y ≤ Z/‖y‖ := by
  have he := tfPotential_nonneg (ae_of_all volume (fun x =>
    jointMasterPosterior_nonneg (graphRawLaw F)
      (fun k : Fin K => dyadicObservationWidth r k) j c₁ r₀ s canonicalRealPacket
      (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z) x)) y
  change 0 ≤ tfPotential (originalQueryDensity F r j c₁ r₀ s z) y at he
  change Z/‖y‖-lam-_ ≤ _
  linarith

theorem OwnProbabilityTailTiltState.event_integral_cap {Z lam r : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (hF : OwnProbabilityTailTiltState Z lam r K p₀ δ F)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (j : Fin (K+1))
    (A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)))
    (hA : MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j] A)
    (hp : p₀ j ≤ (physicalObservationLaw (graphRawLaw F) K).real A)
    {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1) (hry : r₀ ≤ ‖y‖)
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
  have hu := sharp_eventLaw_field_cap hZ hlam F G hGn ell j
    (by rwa [hBA]) (by rwa [hpB]) hlaw hy ha1 hc hcL hr₀ hs hs1 hry hb hba hq hqr hqR hcollar'
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

theorem OwnProbabilityTailTiltState.event_integral_cap_or_floor {Z lam r : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (hF : OwnProbabilityTailTiltState Z lam r K p₀ δ F)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (j : Fin (K+1))
    (A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)))
    (hA : MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j] A)
    {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1) (hry : r₀ ≤ ‖y‖)
    {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y) (hq : 0 < q)
    (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
    (hcollar : localCellRadius y ≤ b^2*(1/(localCellRadius y)^3)) :
    (∫ z in A, originalQueryField F Z lam r j c₁ r₀ s z y
      ∂physicalObservationLaw (graphRawLaw F) K) ≤
    max (p₀ j*(Z/‖y‖)) ((physicalObservationLaw (graphRawLaw F) K).real A*
      originalFieldCapBudget ((2:ℝ)^j.val*r)
        ((physicalObservationLaw (graphRawLaw F) K).real A) δ c₁ r₀ s y b q) := by
  by_cases hp : p₀ j ≤ (physicalObservationLaw (graphRawLaw F) K).real A
  · exact (hF.event_integral_cap hZ hlam h₀ hc hcL hr₀ hs hs1 j A hA hp
      hy ha1 hry hb hba hq hqr hqR hcollar).trans (le_max_right _ _)
  · apply le_trans _ (le_max_left _ _)
    calc
      _ ≤ ∫ _z in A, Z/‖y‖ ∂physicalObservationLaw (graphRawLaw F) K := by
        apply integral_mono_ae
          (originalQueryField_integrable F Z lam r j hc hr₀ hs y).integrableOn
          (integrable_const _)
        exact ae_of_all _ (fun z => originalQueryField_le_nuclear F Z r hlam.le j c₁ r₀ s z y)
      _ = (physicalObservationLaw (graphRawLaw F) K).real A*(Z/‖y‖) := by
        simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_of_not_ge hp) (div_nonneg hZ (norm_nonneg y))

end CoulombAtom

end

end OAI
