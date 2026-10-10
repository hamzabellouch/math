import OAI.Probability.SLE.Multipoint.MultipointActiveCosts
import OAI.Probability.SLE.Multipoint.MultipointPatternProduct

namespace OAI

/-! Integrating the actual phase-selected cost through the individual
live intervals. No common survival endpoint is imposed on all points. -/

noncomputable section
open Set Filter MeasureTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

theorem actual_phase_cost_integral_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) {B : ℝ≥0 → ℝ} (hB : Continuous B)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ*B t) γ G F)
    (hgrowth : PublishedDiskUnivalentGrowth) (J : ℂ → ℂ)
    (hJ : DifferentiableOn ℂ J upperHalfPlane) (hJinj : InjOn J upperHalfPlane)
    (I : Finset ι) (z : ι → ℂ) (hne : Set.InjOn z (I : Set ι))
    (β : ℝ) (hβ : 0 < β) (hdecay : 2*(exponent (greenExponent κ)*β) < 2/κ)
    (a U : ι → ℝ) (hU : ∀ i ∈ I, 0 ≤ U i)
    (σ T : ι → ℝ≥0) (H : ℝ≥0)
    (hσT : ∀ i ∈ I, σ i ≤ T i) (hTH : ∀ i ∈ I, T i ≤ H)
    (hz : ∀ i ∈ I, z i ∈ survivingDomain γ (T i))
    (hstart : ∀ i ∈ I, σ i < T i → logFactorClock κ (logLoewnerCoordinates G (z i) (σ i)) = a i)
    (hend : ∀ i ∈ I, σ i < T i → logFactorClock κ (logLoewnerCoordinates G (z i) (T i))-a i ≤ U i)
    (hgeo : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → σ i < T i → σ j < T j →
      physicalConformalRadius J G (σ i) (z i) ≤ dist (J (z i)) (J (z j)))
    (Q : ℝ → ι → ℂ × ℝ) (j : ℝ → ι → Fin 4)
    (hj : ∀ t ∈ Ico 0 (H : ℝ), patternActiveSet (j t) ⊆ I)
    (hactive : ∀ t ∈ Ico 0 (H : ℝ), ∀ i ∈ patternActiveSet (j t),
      (σ i : ℝ) ≤ t ∧ t ≤ (T i : ℝ))
    (hQ : ∀ t ∈ Ico 0 (H : ℝ), ∀ i ∈ patternActiveSet (j t),
      Q t i = logLoewnerCoordinates G (z i) t)
    (hreg : ∀ t ∈ Ico 0 (H : ℝ), ∀ i ∈ patternActiveSet (j t),
      branchRegulator κ (phaseRegulatorScale β (a i) (U i) (j t i))
        (phaseRegulatorSlope β (j t i)) (Q t i) =
          regulator β (U i) (logFactorClock κ (logLoewnerCoordinates G (z i) t)-a i))
    (R : ℝ → ℝ) (hR : IntervalIntegrable R volume 0 (H : ℝ))
    (hcost : ∀ t ∈ Ico 0 (H : ℝ), R t =
      productDriftCost (patternActiveSet (j t)) κ
        (fun i => phaseRegulatorScale β (a i) (U i) (j t i))
        (fun i => phaseRegulatorSlope β (j t i)) (Q t) (B t.toNNReal)) :
    (∫ t in (0 : ℝ)..(H : ℝ), R t) ≤ uniformDiscountBudget κ β I := by
  have hp : 0 < greenExponent κ := by
    unfold greenExponent
    rw [sub_pos, lt_div_iff₀ hκ]
    linarith
  let f := fun i => actualSingleCost κ β (a i) (U i) B G (z i)
  let g := fun ij : ι × ι => actualPairCost κ β (a ij.1) (a ij.2)
    (U ij.1) (U ij.2) B G (z ij.1) (z ij.2)
  let c := fun ij : ι × ι => overlapStart (σ ij.1) (σ ij.2)
  let d := fun ij : ι × ι => overlapEnd (σ ij.1) (σ ij.2) (T ij.1) (T ij.2)
  have hf (i) (hi : i ∈ I) := actualSingleCost_bound hκ hB hw (σ i) (T i) (hσT i hi)
    (z i) (hz i hi) β (a i) (U i) hβ (hU i hi) (hstart i hi) (hend i hi)
  have hg (ij : ι × ι) (hij : ij ∈ I.offDiag) :
      IntervalIntegrable (g ij) volume (c ij : ℝ) (d ij : ℝ) ∧
        (∫ t in (c ij : ℝ)..(d ij : ℝ), g ij t) ≤
          interactionBudget 2 (exponent (greenExponent κ)*(κ*β)) := by
    obtain ⟨hi,hj,hneij⟩ := Finset.mem_offDiag.mp hij
    exact actualPairCost_bound hκ hB hw hgrowth J hJ hJinj (σ ij.1) (σ ij.2)
      (T ij.1) (T ij.2) (z ij.1) (z ij.2) (hz _ hi) (hz _ hj)
      (fun he => hneij (hne hi hj he)) β (a ij.1) (a ij.2) (U ij.1) (U ij.2)
      hβ.le (exponent_pos hp).le hdecay (hstart _ hi) (hstart _ hj)
      (hgeo _ hi _ hj hneij) (fun h₁ h₂ => by
        simpa only [dist_comm] using hgeo _ hj _ hi hneij.symm h₂ h₁)
  have hcH (ij : ι × ι) (hij : ij ∈ I.offDiag) : c ij ≤ H := by
    obtain ⟨hi,hj,_⟩ := Finset.mem_offDiag.mp hij
    exact max_le ((hσT _ hi).trans (hTH _ hi)) ((hσT _ hj).trans (hTH _ hj))
  have hdH (ij : ι × ι) (hij : ij ∈ I.offDiag) : d ij ≤ H := by
    obtain ⟨hi,_,_⟩ := Finset.mem_offDiag.mp hij
    exact max_le (hcH ij hij) ((min_le_left _ _).trans (hTH _ hi))
  apply integrated_uniform_discount_le hκ hκ8 β I (fun i => (σ i : ℝ))
    (fun i => (T i : ℝ)) (fun ij => (c ij : ℝ)) (fun ij => (d ij : ℝ)) H H.coe_nonneg f g
    (fun i _ => (σ i).coe_nonneg) (fun i hi => by exact_mod_cast hσT i hi)
    (fun i hi => by exact_mod_cast hTH i hi)
    (fun ij _ => (c ij).coe_nonneg) (fun ij _ => by exact_mod_cast le_max_left (c ij) (min (T ij.1) (T ij.2)))
    (fun ij hij => by exact_mod_cast hdH ij hij)
    (fun i hi => (hf i hi).1) (fun ij hij => (hg ij hij).1)
    (fun i hi => (hf i hi).2) (fun ij hij => (hg ij hij).2) R hR
  have hnσ : ∀ᵐ t : ℝ, ∀ i, t ≠ (σ i : ℝ) :=
    ae_all_iff.mpr (fun i => volume.ae_ne (σ i : ℝ))
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (volume.ae_ne (H : ℝ)), ae_restrict_of_ae hnσ] with t ht hneH hnσ
  have ht' : t ∈ Ico 0 (H : ℝ) := ⟨ht.1, lt_of_le_of_ne ht.2 hneH⟩
  rw [hcost t ht']
  have his (i : ι) (hi : i ∈ patternActiveSet (j t)) : t ∈ Ioc (σ i : ℝ) (T i : ℝ) :=
    ⟨lt_of_le_of_ne (hactive t ht' i hi).1 (hnσ i).symm, (hactive t ht' i hi).2⟩
  apply productDriftCost_le_active_envelope hκ hκ8 (hj t ht')
    (fun i => phaseRegulatorScale β (a i) (U i) (j t i))
    (fun i => phaseRegulatorSlope β (j t i)) (fun i _ => phaseRegulatorScale_pos _ _ _ _)
    (Q t) (B t.toNNReal) t (fun i => (σ i : ℝ)) (fun i => (T i : ℝ))
    (fun ij => (c ij : ℝ)) (fun ij => (d ij : ℝ)) f g
    (fun i _ => actualSingleCost_nonneg _ _ _ _ _ _ _ _)
    (fun ij _ => actualPairCost_nonneg _ _ _ _ _ _ _ _ _ _ _) his
  · intro ij hij
    obtain ⟨hi,hj,_⟩ := Finset.mem_offDiag.mp hij
    refine ⟨?_,?_⟩
    · exact max_lt (his _ hi).1 (his _ hj).1
    · exact (le_min (his _ hi).2 (his _ hj).2).trans (by exact_mod_cast le_max_right (c ij) (min (T ij.1) (T ij.2)))
  · intro i hi
    rw [hreg t ht' i hi, hQ t ht' i hi]
    rfl
  · intro ij hij
    obtain ⟨hi,hj,_⟩ := Finset.mem_offDiag.mp hij
    rw [hreg t ht' _ hi, hreg t ht' _ hj, hQ t ht' _ hi, hQ t ht' _ hj]
    rfl

end SLEExactGauge.Multipoint

end

end OAI
