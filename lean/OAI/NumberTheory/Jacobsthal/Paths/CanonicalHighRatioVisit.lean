import OAI.NumberTheory.Jacobsthal.Renewal.FullOccupationRatioTail

namespace OAI

namespace Erdos970


open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace ErdosHighRatioBandTail
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels
open NumberTheoryLean.FiniteHistoryTransport NumberTheoryLean.OccupationDecomposition

def positiveVisit (E : Set CostState) (N : ℕ) : Set (∀ _ : Finset.Iic N, CostState) :=
  ⋃ j : Fin N, {path | path ⟨j.1+1,Finset.mem_Iic.mpr (Nat.succ_le_of_lt j.2)⟩ ∈ E}

theorem positiveVisit_measurable {E : Set CostState} (hE : MeasurableSet E) (N : ℕ) :
    MeasurableSet (positiveVisit E N) :=
  MeasurableSet.iUnion (fun _ => (measurable_pi_apply _) hE)

theorem mem_positiveVisit (E : Set CostState) (N : ℕ)
    (path : ∀ _ : Finset.Iic N, CostState) :
    path ∈ positiveVisit E N ↔ ∃ k : Finset.Iic N, 0 < k.1 ∧ path k ∈ E := by
  constructor
  · intro h
    obtain ⟨j,hj⟩ := mem_iUnion.mp h
    exact ⟨⟨j.1+1,Finset.mem_Iic.mpr (Nat.succ_le_of_lt j.2)⟩,Nat.zero_lt_succ j.1,hj⟩
  · rintro ⟨k,hk,hE⟩
    let j : Fin N := ⟨k.1-1,by have := Finset.mem_Iic.mp k.2; omega⟩
    apply mem_iUnion.mpr
    refine ⟨j,?_⟩
    have he : (⟨j.1+1,Finset.mem_Iic.mpr (Nat.succ_le_of_lt j.2)⟩ : Finset.Iic N)=k := by
      apply Subtype.ext
      dsimp [j]
      omega
    change path _ ∈ E
    rwa [he]

theorem positiveVisit_zero (E : Set CostState) : positiveVisit E 0 = ∅ := by
  ext path
  simp [positiveVisit]

theorem canonical_coordinate_law (s : State) (N k : ℕ) (hk : k ≤ N) :
    (finitePathMeasure s N).map (fun path => path ⟨k,Finset.mem_Iic.mpr hk⟩) =
      (costKernel^k) (s,0) := by
  have h := pathMeasure_coordinate costKernel N k hk (fun _ => (s,0))
  have hkernel : pastKernel costKernel = historyKernel := by
    funext n
    rfl
  unfold pathKernel at h
  rw [hkernel] at h
  simpa only [finitePathMeasure, finitePathKernel, last] using h

theorem positiveVisit_le_fullOccupation (s : State) (N : ℕ) {E : Set CostState}
    (hE : MeasurableSet E) :
    finitePathMeasure s N (positiveVisit E N) ≤ fullOccupation (s,0) E := by
  calc
    _ ≤ ∑ j : Fin N, finitePathMeasure s N
        {path | path ⟨j.1+1,Finset.mem_Iic.mpr (Nat.succ_le_of_lt j.2)⟩ ∈ E} :=
      measure_iUnion_fintype_le (finitePathMeasure s N) _
    _ = ∑ j : Fin N, (costKernel^(j.1+1)) (s,0) E := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← canonical_coordinate_law s N (j.1+1) (Nat.succ_le_of_lt j.2)]
      have hm : Measurable (fun path : (∀ _ : Finset.Iic N, CostState) =>
          path ⟨j.1+1,Finset.mem_Iic.mpr (Nat.succ_le_of_lt j.2)⟩) := measurable_pi_apply _
      exact (Measure.map_apply hm hE).symm
    _ ≤ ∑' k : ℕ, (costKernel^(k+1)) (s,0) E := by
      rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (costKernel^(k+1)) (s,0) E) N]
      exact ENNReal.sum_le_tsum (Finset.range N)
    _ = fullOccupation (s,0) E := by
      rw [fullOccupation, Kernel.sum_apply' _ _ hE]

theorem uniform_canonical_visit_tail (h eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ T : ℝ in atTop, ∀ v : ℝ, ∀ s : EvenState,
      199/100 ≤ s.1 → s.1 ≤ 23/10 → ∀ N : ℕ,
      finitePathMeasure (.inl s) N (positiveVisit (highBand T v h) N) ≤ ENNReal.ofReal eps := by
  filter_upwards [uniform_full_occupation_tail h eps heps] with T hT
  intro v s hsL hsU N
  exact (positiveVisit_le_fullOccupation (.inl s) N (highBand_measurable T v h)).trans
    (hT v s hsL hsU)

theorem exists_canonical_visit_threshold (h eps : ℝ) (heps : 0 < eps) :
    ∃ T₀ : ℝ, 3 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ v : ℝ, ∀ s : EvenState,
      199/100 ≤ s.1 → s.1 ≤ 23/10 → ∀ N : ℕ,
      finitePathMeasure (.inl s) N (positiveVisit (highBand T v h) N) ≤ ENNReal.ofReal eps := by
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp (uniform_canonical_visit_tail h eps heps)
  refine ⟨max T₀ 3,le_max_right _ _,?_⟩
  intro T hT
  exact hT₀ T ((le_max_left _ _).trans hT)

end ErdosHighRatioBandTail


end Erdos970

end OAI
