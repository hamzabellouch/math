import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.RegionEdges
import OAI.Geometry.Cannon.PlanarGraphs.ChartLabel

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

namespace CannonEmbeddedArc.Arc
open Set Topology CannonFaceIncidence unitInterval

variable {ι X D : Type*} [Fintype ι] [TopologicalSpace X] [T2Space X]
  [TopologicalSpace D] [DiscreteTopology D]

omit [Fintype ι] [T2Space X] in
lemma pullChart_union_compl (e : ℂ → X) (he : IsEmbedding e) (F : ι → Arc X)
    (hF : ∀ i, range (F i)⊆range e) :
    (⋃ i,range (pullChart e he (F i) (hF i)))ᶜ=e ⁻¹' (⋃ i,range (F i))ᶜ := by
  simp only [pullChart_range,preimage_compl,preimage_iUnion]

theorem chart_tame_face_structure (e : ℂ → X) (he : IsOpenEmbedding e)
    (F : ι → Arc X) (hrange : ∀ i, range (F i)⊆range e)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ))
    (hQ : ∀ i, e ⁻¹' range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {π : ((⋃ j,range (F j))ᶜ : Set X) → D} (hπ : Continuous π) :
    ∃ (S : D → Set ι) (labels : ι → Bool → D),
      (∀ d, closure (region _ π d)=region _ π d∪⋃ i∈S d,range (F i)) ∧
      (∀ d i, i∈S d ↔ d∈range (labels i)) := by
  let Fc : ι → Arc ℂ := fun i => pullChart e he.isEmbedding (F i) (hrange i)
  have heFc (i : ι) (t : I) : e (Fc i t)=F i t := map_pullChart e he.isEmbedding (F i) (hrange i) t
  have hEq : (⋃ i,range (Fc i))ᶜ=e ⁻¹' (⋃ i,range (F i))ᶜ :=
    pullChart_union_compl e he.isEmbedding F hrange
  let πc := labelPull e hEq π
  have hπc : Continuous πc := labelPull_continuous e he.continuous hEq hπ
  have hFc : Pairwise (fun i j => Compatible (Fc i) (Fc j)) := by
    intro i j hij
    exact pullChart_compatible e he.isEmbedding (F i) (F j) (hrange i) (hrange j) (hF hij)
  have hQc : ∀ i, range (Fc i)⊆⋃ q∈Q,segment ℝ q.1 q.2 := by
    intro i
    rw [show range (Fc i)=e ⁻¹' range (F i) from pullChart_range ..]
    exact hQ i
  choose labels hlabels using tame_edge_incident_labels Fc hFc Q hQc hπc
  refine ⟨fun d => regionEdges Fc πc d,labels,?_,?_⟩
  · intro d
    have hc := tame_region_closure Fc hFc Q hQc hπc d
    have hinc : ∀ z, incident _ πc z=incident _ π (e z) :=
      incident_labelPull e he.isOpenMap he.continuous hEq π
    apply Subset.antisymm
    · intro x hx
      by_cases hxR : x∈region _ π d
      · exact Or.inl hxR
      have hxK : x∈⋃ i,range (F i) := by
        by_contra hn
        exact hxR (closure_region_inside
          (isClosed_iUnion_of_finite (fun i => (F i).compact_range.isClosed)).isOpen_compl hπ hx hn)
      obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hxK
      have hx' : Fc i t∈closure (region _ πc d) := by
        change d∈incident _ πc (Fc i t)
        rw [hinc,heFc]
        exact hx
      rw [hc] at hx'
      rcases hx' with hx'|hx'
      · have hx'' := hx'
        rw [show region _ πc d=e ⁻¹' region _ π d from region_labelPull e hEq π d] at hx''
        exact (hxR (by simpa only [mem_preimage,heFc] using hx'')).elim
      · right
        obtain ⟨j,hj,s,hs⟩ := mem_iUnion₂.mp hx'
        exact mem_iUnion₂.mpr ⟨j,hj,s,by simpa only [heFc] using congrArg e hs⟩
    · rintro x (hx|hx)
      · exact subset_closure hx
      · obtain ⟨i,hi,t,rfl⟩ := mem_iUnion₂.mp hx
        have hx' := region_edge_in_closure Fc hFc Q hQc hπc hi (mem_range_self t)
        change d∈incident _ πc (Fc i t) at hx'
        rw [hinc,heFc] at hx'
        exact hx'
  · intro d i
    constructor
    · rintro ⟨t,ht₀,ht₁,ht⟩
      rwa [hlabels i t ht₀ ht₁] at ht
    · intro hd
      let t : I := ⟨1/2,by constructor <;> norm_num⟩
      have ht₀ : (0:I)<t := by change (0:ℝ)<1/2; norm_num
      have ht₁ : t<(1:I) := by change (1/2:ℝ)<1; norm_num
      refine ⟨t,ht₀,ht₁,?_⟩
      rwa [hlabels i t ht₀ ht₁]

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

end OAI
