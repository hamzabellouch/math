import OAI.Analysis.CircleDomains.Topology.CountableBandNeighborhoods
import OAI.Analysis.CircleDomains.Topology.PathTags

namespace OAI

/-! Combining all open tags with the residual constraint gives a null
free trace for the complete coded path. No incidence measurability is
assumed for this pathwise outer-measure argument. -/

open Set MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem tagged_free_trace_null
    {X : Type*} [TopologicalSpace X] (B Free : Set X) (hFree : Free ⊆ B)
    (Γ : TaggedPath X) (w : X → UnitAddCircle)
    (hresidual : volume (w '' (Γ.1 '' residualTimes B Γ ∩ Free)) = 0)
    (htags : ∀ k, volume (w ''
      (Γ.1 '' Ioo (tagLeft (Γ.2 k)) (tagRight (Γ.2 k)) ∩ Free)) = 0) :
    volume (w '' (range Γ.1 ∩ Free)) = 0 := by
  apply measure_mono_null (t := (w '' (Γ.1 '' residualTimes B Γ ∩ Free)) ∪
    ⋃ k, w '' (Γ.1 '' Ioo (tagLeft (Γ.2 k)) (tagRight (Γ.2 k)) ∩ Free))
  · rintro _ ⟨x, ⟨⟨t, rfl⟩, hx⟩, rfl⟩
    by_cases ht : ∃ k, t ∈ Ioo (tagLeft (Γ.2 k)) (tagRight (Γ.2 k))
    · obtain ⟨k, hk⟩ := ht
      exact Or.inr (mem_iUnion.mpr ⟨k, Γ.1 t, ⟨⟨t, hk, rfl⟩, hx⟩, rfl⟩)
    · apply Or.inl
      refine ⟨Γ.1 t, ⟨⟨t, ?_, rfl⟩, hx⟩, rfl⟩
      rw [residualTimes_eq]
      exact ⟨hFree hx, fun h => ht (mem_iUnion.mp h)⟩
  · exact measure_union_null hresidual (measure_iUnion_null htags)

theorem free_level_incidence_null_of_trace
    {X T : Type*} [TopologicalSpace X] [MeasurableSpace T]
    (ν : Measure T) (γ : C(PathTime, X)) (Free : Set X) (w : X → T)
    (H : Set (T × X)) (hlevel : ∀ x ∈ Free, ∀ t, (t, x) ∈ H → w x = t)
    (htrace : ν (w '' (range γ ∩ Free)) = 0) :
    ν {t | ∃ x ∈ range γ ∩ Free, (t, x) ∈ H} = 0 := by
  apply measure_mono_null _ htrace
  rintro t ⟨x, hx, hxt⟩
  exact ⟨x, hx, hlevel x hx.2 t hxt⟩

end CircleDomainRigidity

end OAI
