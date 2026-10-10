import OAI.Probability.SLE.Multipoint.MultipointSwitches

namespace OAI

/-! The active/completed/midpoint pattern at a switch is a finite,
stopped-past measurable partition. This supplies the actual branch events
for the finite-field conditional optional inequality. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace SLEExactGauge.Multipoint

def switchPatternEvent {Ω ι : Type*} (s : Finset ι)
    (ρ : ι → Ω → ℝ≥0) (τ : Ω → ℝ≥0) (A : Finset ι) : Set Ω :=
  {ω | ∀ i ∈ s, ρ i ω ≤ τ ω ↔ i ∈ A}

theorem switchPatternEvent_measurable {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (s : Finset ι)
    (ρ : ι → Ω → ℝ≥0) (τ : Ω → ℝ≥0)
    (hρ : ∀ i ∈ s, IsStoppingTime ℱ (fun ω => (ρ i ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) (A : Finset ι) :
    MeasurableSet[hτ.measurableSpace] (switchPatternEvent s ρ τ A) := by
  classical
  have he : switchPatternEvent s ρ τ A = ⋂ i ∈ s,
      if i ∈ A then {ω | ρ i ω ≤ τ ω} else {ω | ρ i ω ≤ τ ω}ᶜ := by
    ext ω
    simp only [switchPatternEvent, mem_ofPred_eq, mem_iInter]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro _
    by_cases hi : i ∈ A <;> simp [hi]
  rw [he]
  apply s.measurableSet_biInter
  intro i hi
  have hm : MeasurableSet[hτ.measurableSpace] {ω | ρ i ω ≤ τ ω} := by
    simpa only [WithTop.coe_le_coe] using (hρ i hi).measurableSet_stopping_time_le hτ
  split_ifs
  · exact hm
  · exact hm.compl

theorem switchPatternEvent_unique {Ω ι : Type*} [DecidableEq ι] (s : Finset ι)
    (ρ : ι → Ω → ℝ≥0) (τ : Ω → ℝ≥0) {A B : Finset ι}
    (hA : A ⊆ s) (hB : B ⊆ s) {ω : Ω}
    (hωA : ω ∈ switchPatternEvent s ρ τ A)
    (hωB : ω ∈ switchPatternEvent s ρ τ B) : A = B := by
  apply Finset.ext
  intro i
  by_cases hi : i ∈ s
  · exact (hωA i hi).symm.trans (hωB i hi)
  · exact iff_of_false (fun h => hi (hA h)) (fun h => hi (hB h))

theorem switchPatternEvent_cover {Ω ι : Type*} [DecidableEq ι] (s : Finset ι)
    (ρ : ι → Ω → ℝ≥0) (τ : Ω → ℝ≥0) (ω : Ω) :
    ∃ A ∈ s.powerset, ω ∈ switchPatternEvent s ρ τ A := by
  refine ⟨s.filter (fun i => ρ i ω ≤ τ ω), Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
  intro i hi
  simp only [Finset.mem_filter, hi, true_and]

theorem sum_switchPattern_fields {Ω ι : Type*} [DecidableEq ι] (s : Finset ι)
    (ρ : ι → Ω → ℝ≥0) (τ : Ω → ℝ≥0) (F : Finset ι → Ω → ℝ)
    (X : Ω → ℝ)
    (hF : ∀ A ∈ s.powerset, ∀ ω ∈ switchPatternEvent s ρ τ A, F A ω = X ω) :
    (fun ω => ∑ A ∈ s.powerset, (switchPatternEvent s ρ τ A).indicator (F A) ω) = X := by
  classical
  funext ω
  obtain ⟨A, hA, hωA⟩ := switchPatternEvent_cover s ρ τ ω
  rw [Finset.sum_eq_single A]
  · rw [indicator_of_mem hωA, hF A hA ω hωA]
  · intro B hB hBA
    apply indicator_of_notMem
    intro hωB
    exact hBA (switchPatternEvent_unique s ρ τ (Finset.mem_powerset.mp hB)
      (Finset.mem_powerset.mp hA) hωB hωA)
  · exact fun h => False.elim (h hA)

end SLEExactGauge.Multipoint

end

end OAI
