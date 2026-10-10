import Mathlib
import OAI.Analysis.CoulombIonization.Localization.EventLawSelectedMaster
import OAI.Analysis.CoulombIonization.RadialBounds.SharpLocalPotentialBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

lemma masterWidth_cell_bound {c₁ r₀ s : ℝ} (hc : 0 < c₁)
    (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {y : Space} (hry : r₀ ≤ ‖y‖) :
    2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y := by
  have hh := masterWidth_upper hc.le hr hs y
  simp only [masterBaseDistance,max_eq_left hry] at hh
  have hp : s^masterExponent ≤ 1 := Real.rpow_le_one hs.le hs1 masterExponent_nonneg
  have he := mul_le_mul_of_nonneg_left hp (mul_nonneg hc.le (norm_nonneg y))
  norm_num at hcL
  unfold localCellRadius
  nlinarith [norm_nonneg y]

theorem sharp_eventLaw_master_potential {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {N K : ℕ} (F G : fermionGraph N) (hG : ‖fermionGraphValue N G‖^2 = 1)
    (ell : Fin K → ℝ) (j : ℕ) {A : Set (Fin K × (Fin N × Fin 3) → ℝ)}
    (hinfo : MeasurableSet[observationInformation ell j] (physicalObservationEvent ell A))
    (hp : 0 < physicalObservationProbability F ell A)
    (hlaw : graphRawLaw G = (ENNReal.ofReal (physicalObservationProbability F ell A))⁻¹ •
      Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict
        (physicalObservationEvent ell A)))
    {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (hry : r₀ ≤ ‖y‖)
    {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y) (hq : 0 < q)
    (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
    (hcollar : localCellRadius y ≤ b^2*
      localOffsetMass (max (corePriceExcess Z lam (graphFormVector G)) 0) y) :
    ∃ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y), ∃ ht : 0 ≤ t,
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
  have ha := localCellRadius_pos hy
  have h7 : 7*b < 5*localCellRadius y := by linarith
  have hsep : 6*localCellRadius y+2*b ≤ ‖y‖ := by
    unfold localCellRadius at *
    nlinarith [norm_nonneg y]
  obtain ⟨t,ht,ht0,he⟩ := eventLaw_selected_master_density hZ hlam F G hG ell j
    hinfo hp hlaw y hc hcL hr hs hs1 canonicalRealPacket_smooth canonicalRealPacket_compact
    canonicalRealPacket_normalized canonicalRealPacket_radial canonicalRealPacket_support
    ha hb h7 hsep hq hqR
  refine ⟨t,ht,ht0,he.trans (add_le_add ?_ ?_)⟩
  · exact sharp_selected_potential_error hψ hy ha1 hb hba ht ht0 hZ hlam hq hqr hcollar
  · rw [←ordinaryDensity_raw_local_potential hψ.sobolevFermion.sobolevVector y
      (2*masterWidth c₁ r₀ s y)]
    exact sharp_cell_local_potential hψ hy ha1 hZ hlam
      (by linarith [masterWidth_pos hc hr hs y]) (masterWidth_cell_bound hc hcL hr hs hs1 hry)

end CoulombAtom

end

end OAI
