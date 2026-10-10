import OAI.Probability.SLE.Multipoint.MultipointLocalizedState
import OAI.Probability.SLE.Multipoint.MultipointRadiusStatus
import OAI.Probability.SLE.Multipoint.MultipointPhaseRegulator

namespace OAI

/-! The three actual radius stops and their phase identities along the
constructed localized state. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

def factorRadiusLevel (u₀ u₂ : ℝ) (k : Fin 3) : ℝ :=
  if k = 0 then u₀ else if k = 1 then (u₀+u₂)/2 else u₂

lemma factorRadiusLevel_nonneg {u₀ u₂ : ℝ} (h₀ : 0 ≤ u₀) (h₂ : 0 ≤ u₂) (k : Fin 3) :
    0 ≤ factorRadiusLevel u₀ u₂ k := by
  fin_cases k <;> norm_num [factorRadiusLevel] <;> positivity

lemma factorRadiusLevel_monotone {u₀ u₂ : ℝ} (hu : u₀ ≤ u₂) :
    Monotone (factorRadiusLevel u₀ u₂) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [factorRadiusLevel] at * <;> linarith

def actualFactorStops {Ω ι : Type*} (γ : Ω → ℝ≥0 → ℂ)
    (G : Ω → ℝ≥0 → ℂ → ℂ) (z : ι → ℂ) (u₀ u₂ : ι → ℝ) (H : ℝ≥0)
    (k : ι × Fin 3) : Ω → ℝ≥0 :=
  cutoffStop (fun ω => radiusLevelTime (γ ω) (G ω) (z k.1)
    (factorRadiusLevel (u₀ k.1) (u₂ k.1) k.2)) (H+1)

def factorSwitchList {Ω ι : Type*} [Fintype ι]
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) : List (Ω → ℝ≥0) :=
  (fun _ => 0) :: (Finset.univ.toList.map ρ)

lemma factorSwitchList_zero {Ω ι : Type*} [Fintype ι]
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) : (fun _ : Ω => (0 : ℝ≥0)) ∈ factorSwitchList ρ := by
  simp only [factorSwitchList, List.mem_cons, true_or]

lemma factorSwitchList_mem {Ω ι : Type*} [Fintype ι]
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (k : ι × Fin 3) : ρ k ∈ factorSwitchList ρ := by
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨k,Finset.mem_toList.mpr (Finset.mem_univ _),rfl⟩)

lemma factorSwitchList_forall {Ω ι : Type*} [Fintype ι]
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (P : (Ω → ℝ≥0) → Prop)
    (hzero : P (fun _ => 0)) (hρ : ∀ k, P (ρ k)) : ∀ τ ∈ factorSwitchList ρ, P τ := by
  intro τ hτ
  rcases List.mem_cons.mp hτ with rfl | hτ
  · exact hzero
  · obtain ⟨k,_,rfl⟩ := List.mem_map.mp hτ
    exact hρ k

theorem actualFactorStops_regular {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (z : ι → ℂ) (hz : ∀ i, z i ∈ upperHalfPlane) (u₀ u₂ : ι → ℝ)
    (h₀ : ∀ i, 0 ≤ u₀ i) (hu : ∀ i, u₀ i ≤ u₂ i) (H : ℝ≥0) :
    (∀ k, IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (actualFactorStops γ G z u₀ u₂ H k ω : WithTop ℝ≥0))) ∧
    (∀ ω i, Monotone (fun k => actualFactorStops γ G z u₀ u₂ H (i,k) ω)) ∧
    (∀ k ω, actualFactorStops γ G z u₀ u₂ H k ω ≤ H+1) := by
  refine ⟨?_,?_,?_⟩
  · intro k
    exact cutoffStop_stopping _ _ (actual_radiusLevelTime_stopping hB hm hBm hBc hB0 κ hκ hκ8
      γ G F hw (z k.1) (hz k.1) _ (factorRadiusLevel_nonneg (h₀ k.1) ((h₀ k.1).trans (hu k.1)) k.2)) (H+1)
  · intro ω i j k hjk
    apply cutoffStop_mono _ (H+1) ω
    intro ω'
    exact radiusLevelTime_mono (continuous_const.mul (hBc ω')) (hw ω') (z i)
      (factorRadiusLevel_nonneg (h₀ i) ((h₀ i).trans (hu i)) j)
      (factorRadiusLevel_monotone (hu i) hjk)
  · exact fun k ω => cutoffStop_le_horizon _ _ ω

lemma LocalizedState.actual_at {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi M : ℝ} {H : ℝ≥0} {z : ι → ℂ} {τ : ι → Ω → ℝ≥0}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (S : LocalizedState B hm κ lo hi M H z τ γ G)
    (ω : Ω) (i : ι) (t : ℝ≥0) (htχ : t ≤ S.χ ω) (htτ : t ≤ τ i ω) :
    z i ∈ survivingDomain (γ ω) t ∧ S.Q t ω i = logLoewnerCoordinates (G ω) (z i) t := by
  have ht : t ≤ min (τ i ω) (S.χ ω) := le_min htτ htχ
  exact ⟨survivingDomain_antitone (γ ω) ht (S.actual ω i).1,
    (S.actual ω i).2 ⟨t.coe_nonneg, by exact_mod_cast ht⟩⟩

theorem actual_phase_regulator
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    {κ lo hi M β : ℝ} (hκ : 0 < κ) (hβ : 0 ≤ β) {H : ℝ≥0}
    {z : ι → ℂ} {u₀ u₂ : ι → ℝ} (h₀ : ∀ i, 0 ≤ u₀ i) (hu : ∀ i, u₀ i ≤ u₂ i)
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ}
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (S : LocalizedState B hm κ lo hi M H z
      (fun i => actualFactorStops γ G z u₀ u₂ H (i,2)) γ G)
    (horder : ∀ ω i, Monotone (fun k => actualFactorStops γ G z u₀ u₂ H (i,k) ω))
    (ω : Ω) (t : ℝ≥0) (htχ : t ≤ S.χ ω) (i : ι)
    (hactive : phaseActive (phaseAt (actualFactorStops γ G z u₀ u₂ H) t ω i)) :
    let a := sourceClockLevel κ (z i) (u₀ i)
    let U := κ/4*(u₂ i-u₀ i)
    let j := phaseAt (actualFactorStops γ G z u₀ u₂ H) t ω i
    branchRegulator κ (phaseRegulatorScale β a U j) (phaseRegulatorSlope β j) (S.Q t ω i) =
      regulator β U (logFactorClock κ (S.Q t ω i)-a) ∧
    branchRegulator κ (phaseRegulatorScale β a U j) (phaseRegulatorSlope β j) (S.Q t ω i) ≤ 1 := by
  have htt := ((phaseAt_active_iff _ ω i (horder ω i) t).mp hactive).2.le
  obtain ⟨hlive,he⟩ := S.actual_at ω i t htχ htt
  have hh := cutoff_radius_factor_thresholds (continuous_const.mul (hBc ω)) (hw ω) hκ
    (z i) (u₀ i) (u₂ i) (h₀ i) ((h₀ i).trans (hu i)) H t
    (htχ.trans (S.bounded ω)) hlive ω
  dsimp only at hh ⊢
  apply phaseAt_regulator_eq_and_le_one _ ω i (horder ω i) t κ β
    (sourceClockLevel κ (z i) (u₀ i)) (κ/4*(u₂ i-u₀ i)) hβ (S.Q t ω i) hactive
  · intro ht
    rw [he]
    exact hh.1.mp ht
  · intro ht
    rw [he]
    apply le_of_not_gt
    intro h
    exact (not_le_of_gt ht) (hh.2.1.mpr h.le)
  · intro ht
    rw [he]
    exact hh.2.1.mp ht
  · intro ht
    rw [he]
    apply le_of_not_gt
    intro h
    exact (not_le_of_gt ht) (hh.2.2.1.mpr h.le)

theorem actual_phase_switch_clock
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    {κ lo hi M : ℝ} (hκ : 0 < κ) {H : ℝ≥0}
    {z : ι → ℂ} {u₀ u₂ : ι → ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ}
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (S : LocalizedState B hm κ lo hi M H z
      (fun i => actualFactorStops γ G z u₀ u₂ H (i,2)) γ G)
    (horder : ∀ ω i, Monotone (fun k => actualFactorStops γ G z u₀ u₂ H (i,k) ω))
    (ω : Ω) (i : ι) (k : Fin 3)
    (hk : actualFactorStops γ G z u₀ u₂ H (i,k) ω ≤ S.χ ω) :
    logFactorClock κ (S.Q (actualFactorStops γ G z u₀ u₂ H (i,k) ω) ω i)-
      sourceClockLevel κ (z i) (u₀ i) =
      if k = 0 then 0 else if k = 1 then (κ/4*(u₂ i-u₀ i))/2 else κ/4*(u₂ i-u₀ i) := by
  let t := actualFactorStops γ G z u₀ u₂ H (i,k) ω
  have htτ : t ≤ actualFactorStops γ G z u₀ u₂ H (i,2) ω := horder ω i (Fin.le_last k)
  obtain ⟨hlive,he⟩ := S.actual_at ω i t hk htτ
  have hclock := (cutoff_radius_eq_iff (continuous_const.mul (hBc ω)) (hw ω) hκ
    (z i) (factorRadiusLevel (u₀ i) (u₂ i) k) H t (hk.trans (S.bounded ω)) hlive ω).mp rfl
  rw [he,hclock]
  fin_cases k <;> norm_num [factorRadiusLevel, sourceClockLevel] <;> ring

end SLEExactGauge.Multipoint

end

end OAI
