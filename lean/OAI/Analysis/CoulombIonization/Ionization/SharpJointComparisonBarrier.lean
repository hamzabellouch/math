import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.SharpMasterPotentialBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

def radialPatchGapMean {N : ℕ} (ψ : FormVector N) (y : Space) {r b : ℝ}
    (hr0 : 0 ≤ r) (hb : 0 < b) (Z lam : ℝ) : ℝ :=
  ∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
    weightedPatchGap (orderedCutForm (coreFirstRadialCut y hr0 hb)
      (coreFirstRadialCut_partition y hr0 hb) ψ c) s Z lam y (r-4*b) hb
      (radialPatchRetention N y r b c s) u

theorem sharp_joint_selected_patch {N : ℕ} {ψ : FormVector N}
    (hψ : FormAdmissible ψ) {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1)
    {b Z lam q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y)
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hq : 0 < q)
    (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hcollar : localCellRadius y ≤ b^2*localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) :
    ∃ r ∈ Icc (5*localCellRadius y) (6*localCellRadius y), ∃ hr0 : 0 ≤ r,
      radialPatchGapMean ψ y hr0 hb Z lam ≤ corePriceExcess Z lam ψ+
        sharpPatchRemainder (localCellRadius y) b
          (localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) ∧
      radialPotentialError ψ y hr0 hb Z lam q ≤
        sharpPotentialRemainder (localCellRadius y) b
          (localOffsetMass (max (corePriceExcess Z lam ψ) 0) y)
          (max (corePriceExcess Z lam ψ) 0) q := by
  have ha := localCellRadius_pos hy
  have h7 : 7*b < 5*localCellRadius y := by linarith
  have hn : 6*localCellRadius y+2*b ≤ ‖y‖ := by
    unfold localCellRadius at *
    nlinarith [norm_nonneg y]
  have hm : formMass ψ = 1 := hψ.2.2.2.2.1
  obtain ⟨r,hr,hr0,hd,hgap⟩ := selected_fresh_patch_budget_with_deletion
    hψ.sobolevFermion hm y ha hb h7 hn hZ hlam canonicalRealPacket_smooth
    canonicalRealPacket_compact canonicalRealPacket_normalized
    canonicalRealPacket_radial canonicalRealPacket_support
  have hgs : radialPatchGapMean ψ y hr0 hb Z lam ≤
      selectedPatchEnergyError ψ y (localCellRadius y) hr0 hb Z lam canonicalRealPacket := hgap
  refine ⟨r,hr,hr0,hgs.trans (sharp_selected_patch_energy hψ.sobolevFermion hm hy
    hb h7 hr hr0 hZ hlam hcollar),?_⟩
  have htb : 0 < r-7*b := by linarith [hr.1]
  have he := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 2/q))
  have hd' := div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hd) htb.le
  have hpot : radialPotentialError ψ y hr0 hb Z lam q ≤
      selectedPotentialError ψ y (localCellRadius y) hr0 hb Z lam q canonicalRealPacket := by
    simp only [radialPotentialError,hm,Real.sqrt_one,one_mul,mul_one,selectedPotentialError,
      selectedPatchEnergyError]
    exact add_le_add (add_le_add (add_le_add (add_le_add he le_rfl) le_rfl) le_rfl) hd'
  exact hpot.trans (sharp_selected_potential_error hψ hy ha1 hb hba hr hr0 hZ hlam hq hqr hcollar)

theorem sharp_eventLaw_joint_comparison {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
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
    (masterWidth_cell_bound hc hcL hr hs hs1 hry)
  simp only [hm,mul_one] at hcmp
  exact hcmp.trans (add_le_add hpot hraw)

end CoulombAtom

end

end OAI
