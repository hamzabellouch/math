import OAI.Geometry.RCD.Metric.DominatedProbabilityCompactness

namespace OAI

/-! # Weak compactness with a compact fiber and a dominated marginal -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

theorem probability_subsequence_compact_fiber (σ : FiniteMeasure X)
    (P : ℕ → ProbabilityMeasure (X × Y))
    (hP : ∀ k, (P k : Measure (X × Y)).map Prod.fst ≤ σ) :
    ∃ (Q : ProbabilityMeasure (X × Y)) (j : ℕ → ℕ),
      StrictMono j ∧ Tendsto (P ∘ j) atTop (𝓝 Q) := by
  have ht : IsTightMeasureSet {((ρ : ProbabilityMeasure (X × Y)) : Measure (X × Y)) |
      ρ ∈ Set.range P} := by
    apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
    intro ε hε
    obtain ⟨K,hK,hσ⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (isTightMeasureSet_singleton (μ := (σ : Measure X))) ε hε
    refine ⟨K ×ˢ (univ : Set Y),hK.prod isCompact_univ,?_⟩
    rintro μ ⟨ρ,⟨k,rfl⟩,rfl⟩
    have hb := (hP k Kᶜ).trans (hσ σ (by simp))
    rw [Measure.map_apply measurable_fst hK.measurableSet.compl] at hb
    convert hb using 1
    congr 1
    ext z
    simp
  have hc := isCompact_closure_of_isTightMeasureSet ht
  obtain ⟨Q,_,j,hj,hlim⟩ := hc.tendsto_subseq (fun k => subset_closure (mem_range_self k))
  exact ⟨Q,j,hj,hlim⟩

end RegularPointCoordinates

end

end OAI
