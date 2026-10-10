import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.Portion
import OAI.Geometry.Cannon.PlanarGraphs.ComponentRegion

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

theorem tame_pair_jordan_regions (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q∈Q, segment ℝ q.1 q.2) :
    ∃ R : Bool → Set ℂ,
      (∀ i, IsOpen (R i) ∧ IsConnected (R i) ∧
        closure (R i)=R i ∪ (range a∪range b) ∧ frontier (R i)=range a∪range b) ∧
      Disjoint (R false) (R true) ∧ R false∪R true=(range a∪range b)ᶜ := by
  let K : Set ℂ := range a∪range b
  have hK : IsClosed K := a.compact_range.isClosed.union b.compact_range.isClosed
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) := hK.isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents (Kᶜ : Set ℂ)) := inferInstance
  obtain ⟨l,hl⟩ := tame_pair_jordan a b hab₀ hab₁ hc Q ha hb
  let R := fun i => region Kᶜ ConnectedComponents.mk (l i)
  have hRsub (i) : R i⊆Kᶜ := region_subset _ _ _
  have hRclose (i) : closure (R i)=R i∪K := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxK : x∈K
      · exact Or.inr hxK
      · exact Or.inl (closure_region_inside hK.isOpen_compl ConnectedComponents.continuous_coe hx hxK)
    · apply union_subset subset_closure
      intro x hx
      show l i∈incident _ ConnectedComponents.mk x
      rw [hl x hx]
      exact mem_range_self i
  refine ⟨R,fun i => ⟨region_isOpen hK.isOpen_compl ConnectedComponents.continuous_coe _,
    component_region_connected _ _,hRclose i,?_⟩,
    component_regions_disjoint _ (l.injective.ne (by decide)),?_⟩
  · rw [frontier, (region_isOpen hK.isOpen_compl ConnectedComponents.continuous_coe (l i)).interior_eq,
      hRclose i]
    ext x
    simp only [mem_sdiff,mem_union]
    constructor
    · rintro ⟨hx,hn⟩
      exact hx.resolve_left hn
    · intro hx
      exact ⟨Or.inr hx,fun h => hRsub i h hx⟩
  · apply Subset.antisymm (union_subset (hRsub false) (hRsub true))
    intro x hx
    obtain ⟨i,hi⟩ := l.surjective (ConnectedComponents.mk ⟨x,hx⟩)
    cases i
    · exact Or.inl ⟨hx,hi.symm⟩
    · exact Or.inr ⟨hx,hi.symm⟩

theorem connected_obstacle_jordan_side {K : Set ℂ} (hK : IsConnected K) (hKclosed : IsClosed K)
    (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q∈Q, segment ℝ q.1 q.2)
    (hCK : range a∪range b ⊆ Kᶜ) :
    ∃ R : Set ℂ, IsOpen R ∧ IsConnected R ∧ frontier R=range a∪range b ∧
      closure R=R∪(range a∪range b) ∧
      closure R ⊆ connectedComponentIn Kᶜ (a 0) := by
  let C : Set ℂ := range a∪range b
  have hC : IsClosed C := a.compact_range.isClosed.union b.compact_range.isClosed
  let _ : LocallyConnectedSpace (Cᶜ : Set ℂ) := hC.isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents (Cᶜ : Set ℂ)) := inferInstance
  obtain ⟨l,hl⟩ := tame_pair_jordan a b hab₀ hab₁ hc Q ha hb
  have hKC : closure K⊆Cᶜ := by
    rw [hKclosed.closure_eq]
    intro point hpoint hpointC
    exact hCK hpointC hpoint
  obtain ⟨d,hd⟩ := label_on_connected ConnectedComponents.continuous_coe hK.closure hKC
  let i := l.symm d
  let R := region Cᶜ ConnectedComponents.mk (l (!i))
  have hRopen : IsOpen R := region_isOpen hC.isOpen_compl ConnectedComponents.continuous_coe _
  have hRconn : IsConnected R := component_region_connected _ _
  have hRi : R⊆Kᶜ := by
    intro x hx hxK
    obtain ⟨_,he⟩ := hd (subset_closure hxK)
    obtain ⟨_,he'⟩ := hx
    have hh : (!i)=i := l.injective (he'.symm.trans (he.trans (l.apply_symm_apply d).symm))
    cases i <;> simp at hh
  have hRcl : closure R=R∪C := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxC : x∈C
      · exact Or.inr hxC
      · exact Or.inl (closure_region_inside hC.isOpen_compl ConnectedComponents.continuous_coe hx hxC)
    · apply union_subset subset_closure
      intro x hx
      show l (!i)∈incident _ ConnectedComponents.mk x
      rw [hl x hx]
      exact mem_range_self _
  have hclsub : closure R⊆Kᶜ := by rw [hRcl]; exact union_subset hRi hCK
  have hxcl : a 0∈closure R := by rw [hRcl]; exact Or.inr (Or.inl (mem_range_self 0))
  refine ⟨R,hRopen,hRconn,?_,hRcl,
    hRconn.isPreconnected.closure.subset_connectedComponentIn hxcl hclsub⟩
  rw [frontier,hRopen.interior_eq,hRcl]
  ext x
  simp only [mem_sdiff,mem_union]
  constructor
  · rintro ⟨hx,hn⟩
    exact hx.resolve_left hn
  · intro hx
    exact ⟨Or.inr hx,fun h => (region_subset _ _ _ h) hx⟩
end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
