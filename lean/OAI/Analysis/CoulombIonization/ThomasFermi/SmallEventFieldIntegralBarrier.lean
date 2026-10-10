import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.OwnProbabilityFieldCapBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.TinyProbabilityFloorBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped Topology

namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma small_probability_three_quarters {p u : ℝ} (hp : 0 ≤ p) (hu : 0 < u)
    (hpu : p ≤ u^80) : p^(3/4:ℝ) ≤ u^60 := by
  calc _ ≤ (u^80)^(3/4:ℝ) := Real.rpow_le_rpow hp hpu (by norm_num)
       _ = _ := by
         rw [←Real.rpow_natCast,←Real.rpow_mul hu.le]
         norm_num

lemma tiny_floor_normalized_field_bound {Z u : ℝ} {y : Space}
    (hZ : 0 ≤ Z) (hu : 0 < u) (hu1 : u ≤ 1) (huy : u ≤ ‖y‖)
    (hay : localCellRadius y ≤ u) :
    (localCellRadius y)^4*(tinyProbabilityFloor Z u*(Z/‖y‖)) ≤ u^60 := by
  have ha : 0 ≤ localCellRadius y := by unfold localCellRadius; positivity
  have hh := tinyProbabilityFloor_nuclear_bound hZ hu huy
  have h83 : u^83 ≤ u^60 := pow_le_pow_of_le_one hu.le hu1 (by norm_num : 60 ≤ 83)
  calc
    _ ≤ (localCellRadius y)^4*u^79 := mul_le_mul_of_nonneg_left hh (pow_nonneg ha _)
    _ ≤ u^4*u^79 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hay 4) (by positivity)
    _ = u^83 := by ring
    _ ≤ _ := h83

theorem OwnProbabilityTailTiltState.small_event_integral {Z lam r : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hr : 0 < r) {N K : ℕ} {F : fermionGraph N}
    {δ c₁ r₀ s : ℝ}
    (hF : OwnProbabilityTailTiltState Z lam r K
      (fun j => tinyProbabilityFloor Z ((2:ℝ)^j.val*r)) δ F)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (j : Fin (K+1)) {y : Space}
    (huy : (2:ℝ)^j.val*r ≤ ‖y‖) (hyu : ‖y‖ ≤ 2*((2:ℝ)^j.val*r))
    (hu1 : (2:ℝ)^j.val*r ≤ 1) (hry : r₀ ≤ ‖y‖)
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
  have hy : y ≠ 0 := norm_pos_iff.mp (hu.trans_le huy)
  have ha := localCellRadius_pos hy
  have hC := tfPatchCapConstant_pos
  have hfloor : 0 < tinyProbabilityFloor Z u := tinyProbabilityFloor_pos hZ hu
  by_cases hp : tinyProbabilityFloor Z u ≤ p
  · have hpp : 0 < p := hfloor.trans_le hp
    have hh := hF.event_integral_cap hZ hlam
      (fun _ => tinyProbabilityFloor_pos hZ (by positivity)) hc hcL hr₀ hs hs1 j A hA hp
      hy hgeom.radius_le hry hgeom.cut_pos hgeom.cut_le hgeom.probe_pos
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
    have hb := tiny_floor_normalized_field_bound hZ hu hu1 huy (band_local_radius_le hu.le hyu)
    calc _ ≤ _ := mul_le_mul_of_nonneg_left hh (pow_nonneg ha.le 4)
         _ ≤ u^60 := hb
         _ ≤ _ := by dsimp only [u]; nlinarith [pow_nonneg hu.le 60]

end CoulombAtom

end

end OAI
