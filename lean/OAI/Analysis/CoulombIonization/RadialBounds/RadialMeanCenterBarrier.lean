import Mathlib
import OAI.Analysis.CoulombIonization.Localization.ActualTailStateCapBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_RadialMeanCenter_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators NNReal

open CoulombAnalysis CoulombNeumann

lemma radial_coreSlice_zero {N : ℕ} (ψ : FormVector N) (y : Space) {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
    (u : Configuration (cutOutNumber c)) (v : Configuration (cutCoreNumber c))
    (i : Fin (cutCoreNumber c)) (hi : v i ∉ radialPatchCore y t) :
    FormZeroAt (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u) v := by
  apply FormZeroAt.coreSlice
  exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
    (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
    (joinLists v u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)

 theorem radial_high_mean_expected_center {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {k : Space → ℝ} {L : ℝ≥0} (hk : LipschitzWith L k) (hkn : ∀ x, 0 ≤ k x)
    {q H eta m : ℝ} (hq : 0 < q) (hs : Function.support k ⊆ closedBall 0 q)
    (hqR : q ≤ (t-4*b)/12) (hsmall : tfPatchOscillationConstant/(t-4*b)*q ≤ 1/2)
    (hH : 0 ≤ H) (heta : 0 < eta) (hm : 0 < m)
    (hcount : ∀ c : Fin N → Fin 2, ∀ s : Spins (cutOutNumber c), ∀ᵐ u,
      formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) ψ c) s u) ≠ 0 →
      m ≤ ∫ z in ball (0 : Space) q,
        retainedPatchLp hb (radialPatchRetention N y t b c s u) u y (t-4*b) z ∂ballMeasure (t-4*b))
    (hhigh : ∀ c : Fin N → Fin 2, ∀ s : Spins (cutOutNumber c), ∀ᵐ u,
      formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) ψ c) s u) ≠ 0 →
      (max (H+(tfPatchOscillationConstant/(t-4*b)*q)*(t-4*b)⁻¹^4) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
        (∫ x, k x ∂ballMeasure (t-4*b))+Real.sqrt ((16*q^3*(L:ℝ)^2)*eta) <
        ∫ x, k x*retainedPatchLp hb (radialPatchRetention N y t b c s u) u y (t-4*b) x
          ∂ballMeasure (t-4*b)) :
    H*formMass ψ-(H/eta+2/m)*radialPatchGapMean ψ y ht hb Z lam-
      (2*(tfPatchOscillationConstant/(t-4*b)*q)*(t-4*b)⁻¹^4)*formMass ψ ≤
      expectedRadialPatchCenter ψ y ht hb Z lam := by
  have hR : 0 < t-4*b := by linarith
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  have hχ (c : Fin N → Fin 2) := orderedCutForm_sobolev p hp hψ.sobolevVector c
  have hbound (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :=
    conditional_high_mean_expected_center_on_support (hχ c) s (radialPatchCore y t)
      (radial_coreSlice_zero ψ y ht hb c s) y hR hb
      (radialPatch_nuclear_distance hb hy) (radialPatch_core_distance y hb) Z lam
      (radialPatchRetention N y t b c s)
      (radial_weightedPatchGap_integrable hψ y ht hb htb hy hZ hlam canonicalRealPacket_smooth
        canonicalRealPacket_compact canonicalRealPacket_normalized canonicalRealPacket_radial
        canonicalRealPacket_support c s)
      hk hkn hq hs hqR hsmall hH heta hm (hcount c s) (hhigh c s)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s _ => hbound c s))
  simp_rw [Finset.sum_sub_distrib,←Finset.mul_sum] at hh
  simp_rw [(hχ _).integral_coreSlice_mass] at hh
  rw [orderedCutForm_mass_sum p hp hψ.sobolevVector] at hh
  exact hh

 theorem radial_low_mean_expected_center {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {k : Space → ℝ} {L : ℝ≥0} (hk : LipschitzWith L k) (hkn : ∀ x, 0 ≤ k x)
    {q H eta : ℝ} (hq : 0 < q) (hs : Function.support k ⊆ closedBall 0 q)
    (hqR : q ≤ (t-4*b)/12) (hH : 0 ≤ H) (heta : 0 < eta)
    (hlow : ∀ c : Fin N → Fin 2, ∀ s : Spins (cutOutNumber c), ∀ᵐ u,
      formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) ψ c) s u) ≠ 0 →
      (∫ x, k x*retainedPatchLp hb (radialPatchRetention N y t b c s u) u y (t-4*b) x
          ∂ballMeasure (t-4*b))+Real.sqrt ((16*q^3*(L:ℝ)^2)*eta) <
      (max (H-(tfPatchOscillationConstant/(t-4*b)*q)*(t-4*b)⁻¹^4) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
        (∫ x, k x ∂ballMeasure (t-4*b))) :
    expectedRadialPatchCenter ψ y ht hb Z lam ≤
      H*formMass ψ+((tfPatchCapConstant/(t-4*b)^4)/eta)*radialPatchGapMean ψ y ht hb Z lam := by
  have hR : 0 < t-4*b := by linarith
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  have hχ (c : Fin N → Fin 2) := orderedCutForm_sobolev p hp hψ.sobolevVector c
  have hbound (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :=
    conditional_low_mean_expected_center_on_support (hχ c) s (radialPatchCore y t)
      (radial_coreSlice_zero ψ y ht hb c s) y hR hb
      (radialPatch_nuclear_distance hb hy) (radialPatch_core_distance y hb) Z lam
      (radialPatchRetention N y t b c s)
      (radial_weightedPatchGap_integrable hψ y ht hb htb hy hZ hlam canonicalRealPacket_smooth
        canonicalRealPacket_compact canonicalRealPacket_normalized canonicalRealPacket_radial
        canonicalRealPacket_support c s)
      hk hkn hq hs hqR hH heta (hlow c s)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s _ => hbound c s))
  simp_rw [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  simp_rw [(hχ _).integral_coreSlice_mass] at hh
  rw [orderedCutForm_mass_sum p hp hψ.sobolevVector] at hh
  exact hh

end Work_RadialMeanCenter_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget
attribute [local irreducible] radialPatchGapMean expectedRadialPatchCenter corePriceExcess

 theorem TailTiltState.event_radial_comparison {Z lam r : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (hstate : TailTiltState Z lam r K p₀ δ F)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (j : Fin (K+1)) {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1)
    (hry : r₀ ≤ ‖y‖) {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y)
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
  obtain ⟨t,ht,ht0,hgap,hpot⟩ := sharp_eventLaw_joint_comparison hZ hlam F G hGn ell j
    (by rwa [hBA]) (by rwa [hpB]) (by rwa [hBA,hpB]) hy ha1 hc hcL hr₀ hs hs1 hry
    hb hba hq hqr hqR hcollar'
  refine ⟨t,ht,ht0,hGn,hlaw,?_,?_⟩
  · apply hgap.trans
    exact add_le_add ((le_max_left _ _).trans hDE)
      (sharpPatchRemainder_mono (localCellRadius_pos hy) hb
        (le_trans zero_le_one (localOffsetMass_one_le _ y)) (localOffsetMass_mono hDE y))
  · rw [hpB,hBA] at hpot
    exact hpot.trans (sharp_combined_error_mono hy hb hq hDE
      (by linarith [masterWidth_pos hc hr₀ hs y]))

end CoulombAtom

end

end OAI
