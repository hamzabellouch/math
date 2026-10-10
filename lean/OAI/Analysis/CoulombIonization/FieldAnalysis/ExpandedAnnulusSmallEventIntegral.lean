import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.PointInverseEventsCell

namespace OAI

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma tiny_floor_normalized_field_bound_half {Z u : ℝ} {y : Space}
    (hZ : 0 ≤ Z) (hu : 0 < u) (hu1 : u ≤ 1) (huy : u/2 ≤ ‖y‖)
    (hay : localCellRadius y ≤ 1) :
    (localCellRadius y)^4*(tinyProbabilityFloor Z u*(Z/‖y‖)) ≤ 2*u^60 := by
  have ha : 0 ≤ localCellRadius y := by unfold localCellRadius; positivity
  have hn : 0 < ‖y‖ := by linarith
  have htmp := tinyProbabilityFloor_nuclear_bound hZ hu (by linarith : u ≤ 2*‖y‖)
  have hh : tinyProbabilityFloor Z u*(Z/‖y‖) ≤ 2*u^79 := by
    have he : tinyProbabilityFloor Z u*(Z/‖y‖) =
        2*(tinyProbabilityFloor Z u*(Z/(2*‖y‖))) := by ring
    rw [he]
    linarith
  have h79 : u^79 ≤ u^60 := pow_le_pow_of_le_one hu.le hu1 (by norm_num : 60 ≤ 79)
  calc
    _ ≤ (localCellRadius y)^4*(2*u^79) := mul_le_mul_of_nonneg_left hh (pow_nonneg ha _)
    _ ≤ 1^4*(2*u^79) := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hay 4) (by positivity)
    _ ≤ _ := by norm_num; linarith

theorem OwnProbabilityTailTiltState.expandedAnnulus_small_event_integral {Z lam r : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hr : 0 < r) {N K : ℕ} {F : fermionGraph N}
    {δ c₁ r₀ s : ℝ}
    (hF : OwnProbabilityTailTiltState Z lam r K
      (fun j => tinyProbabilityFloor Z ((2:ℝ)^j.val*r)) δ F)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (j : Fin (K+1)) {y : Space}
    (huy : ((2:ℝ)^j.val*r)/2 ≤ ‖y‖)
    (hu1 : (2:ℝ)^j.val*r ≤ 1)
    (hgeom : InverseFiniteGeometry c₁ r₀ s (((2:ℝ)^j.val*r)^(101/100:ℝ)) y)
    (hcap : ∀ p : ℝ, 0 < p → p ≤ ((2:ℝ)^j.val*r)^80 →
      (localCellRadius y)^4*(p*originalFieldCapBudget ((2:ℝ)^j.val*r) p δ c₁ r₀ s y
        ((localCellRadius y)^(6/5:ℝ))
        (localCellRadius y*(localCellRadius y)^masterExponent)) ≤
      p^(3/4:ℝ)*(tfPatchCapConstant+1))
    (A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)))
    (hA : MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j] A)
    (hpA : (physicalObservationLaw (graphRawLaw F) K).real A ≤ ((2:ℝ)^j.val*r)^80) :
    (localCellRadius y)^4*(∫ z in A, originalQueryField F Z lam r j c₁ r₀ s z y
      ∂physicalObservationLaw (graphRawLaw F) K) ≤
      (tfPatchCapConstant+2)*((2:ℝ)^j.val*r)^60 := by
  let u := (2:ℝ)^j.val*r
  let p := (physicalObservationLaw (graphRawLaw F) K).real A
  have hu : 0 < u := by dsimp [u]; positivity
  have hy : y ≠ 0 := norm_pos_iff.mp (by linarith)
  have ha := localCellRadius_pos hy
  have hC := tfPatchCapConstant_pos
  have hfloor : 0 < tinyProbabilityFloor Z u := tinyProbabilityFloor_pos hZ hu
  by_cases hp : tinyProbabilityFloor Z u ≤ p
  · have hpp : 0 < p := hfloor.trans_le hp
    have hh := hF.event_integral_cap_of_cell hZ hlam
      (fun _ => tinyProbabilityFloor_pos hZ (by positivity)) hc hcL hr₀ hs hs1 j A hA hp
      hy hgeom.radius_le (by linarith [hgeom.master_fit,hgeom.cut_pos]) hgeom.cut_pos hgeom.cut_le hgeom.probe_pos
      hgeom.probe_fit hgeom.probe_margin hgeom.collar
    have hmul := mul_le_mul_of_nonneg_left hh (pow_nonneg ha.le 4)
    have hweight := hcap p hpp hpA
    have hpw := small_probability_three_quarters hpp.le hu hpA
    calc _ ≤ _ := hmul
         _ ≤ p^(3/4:ℝ)*(tfPatchCapConstant+1) := hweight
         _ ≤ u^60*(tfPatchCapConstant+1) :=
          mul_le_mul_of_nonneg_right hpw (by linarith)
         _ ≤ _ := by dsimp only [u]; nlinarith [pow_nonneg hu.le 60]
  · have hh : (∫ z in A, originalQueryField F Z lam r j c₁ r₀ s z y
        ∂physicalObservationLaw (graphRawLaw F) K) ≤ tinyProbabilityFloor Z u*(Z/‖y‖) := by
      calc
        _ ≤ ∫ _z in A, Z/‖y‖ ∂physicalObservationLaw (graphRawLaw F) K := by
          apply integral_mono_ae
            (originalQueryField_integrable F Z lam r j hc hr₀ hs y).integrableOn
            (integrable_const _)
          exact ae_of_all _ (fun z => originalQueryField_le_nuclear F Z r hlam.le j c₁ r₀ s z y)
        _ = p*(Z/‖y‖) := by
          simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,p]
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_of_not_ge hp) (div_nonneg hZ (norm_nonneg y))
    have hb := tiny_floor_normalized_field_bound_half hZ hu hu1 huy hgeom.radius_le
    calc _ ≤ _ := mul_le_mul_of_nonneg_left hh (pow_nonneg ha.le 4)
         _ ≤ 2*u^60 := hb
         _ ≤ _ := by dsimp only [u]; nlinarith [pow_nonneg hu.le 60]

end CoulombAtom

end

end OAI
