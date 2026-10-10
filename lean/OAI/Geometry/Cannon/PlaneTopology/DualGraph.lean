import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.PairComponentClosure
import OAI.Geometry.Cannon.PlaneTopology.IncidentFaces
import OAI.Geometry.Cannon.Boundary.GraphReachableCover

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
def dualGraph (F : ι → Arc ℂ) (E : Set ι) : SimpleGraph (Faces F) where
  Adj a b := a≠b ∧ ∃ i∈E,i∈regionEdges F ConnectedComponents.mk a ∧
    i∈regionEdges F ConnectedComponents.mk b
  symm := ⟨by rintro a b ⟨hab,i,hi,ha,hb⟩; exact ⟨hab.symm,i,hi,hb,ha⟩⟩
  loopless := ⟨fun a h=>h.1 rfl⟩

theorem dualGraph_preconnected (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2) :
    (dualGraph F univ).Preconnected := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  let _ : LocallyConnectedSpace ((⋃i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃i,range (F i))ᶜ : Set ℂ)) := inferInstance
  have hcov : (⋃ d:Faces F,closure (face F d))=univ :=
    eq_univ_of_forall fun x=>mem_iUnion.mpr (facial_closures_cover F hF Q hQ x)
  apply CannonClosedCover.graph_reachable_cover (dualGraph F univ) (fun d=>closure (face F d))
    (fun _=>isClosed_closure) (by rw [hcov]; exact isPreconnected_univ)
    (fun d=>(face_nonempty F d).mono subset_closure)
  rintro a b ⟨z,hza,hzb⟩
  by_cases heq : a=b
  · subst b; exact .rfl
  by_cases hzV : Vertex F z
  · obtain ⟨p⟩ := vertexFaceGraph_preconnected F hF Q hQ hzV
      (⟨a,hza⟩ : IncidentFaces F z) ⟨b,hzb⟩
    have hmap {u v : IncidentFaces F z} (p : (vertexFaceGraph F z).Walk u v) :
        (dualGraph F univ).Reachable u.val v.val := by
      induction p with
      | nil => exact .rfl
      | @cons u v w h p ih =>
        obtain ⟨huv,i,hi,hu,hv⟩ := h
        have hh : (dualGraph F univ).Adj u.val v.val :=
          ⟨fun h=>huv (Subtype.ext h),i,mem_univ _,hu,hv⟩
        exact hh.reachable.trans ih
    exact hmap p
  have hzK : z∈⋃i,range (F i) := by
    by_contra hn
    have get (d:Faces F) (hd:z∈closure (face F d)) : z∈face F d := by
      change z∈closure (region ((⋃i,range (F i))ᶜ) ConnectedComponents.mk d) at hd
      rw [tame_region_closure F hF Q hQ ConnectedComponents.continuous_coe d] at hd
      rcases hd with h|h
      · exact h
      · obtain ⟨i,-,hi⟩ := mem_iUnion₂.mp h
        exact (hn (mem_iUnion.mpr ⟨i,hi⟩)).elim
    exact heq ((get a hza).2.symm.trans (get b hzb).2)
  obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hzK
  have ht₀ : 0<t := by
    apply lt_of_le_of_ne (nonneg t)
    intro he
    exact hzV ⟨i,Or.inl (congrArg (F i) (show (0:I)=t from Subtype.ext he))⟩
  have ht₁ : t<1 := by
    apply lt_of_le_of_ne (le_one t)
    intro he
    exact hzV ⟨i,Or.inr (congrArg (F i) (show (1:I)=t from Subtype.ext he.symm))⟩
  exact (show (dualGraph F univ).Adj a b from
    ⟨heq,i,mem_univ _,⟨t,ht₀,ht₁,hza⟩,⟨t,ht₀,ht₁,hzb⟩⟩).reachable

omit [DecidableEq ι] [Nonempty ι] in
theorem complement_preconnected_of_dual [DecidableEq ι] [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (E : Set ι) (hdual : (dualGraph F E).Preconnected) :
    IsPreconnected ((⋃ i∈Eᶜ,range (F i))ᶜ : Set ℂ) := by
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  let _ : LocallyConnectedSpace ((⋃i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃i,range (F i))ᶜ : Set ℂ)) := inferInstance
  let X : Set ℂ := (⋃ i∈Eᶜ,range (F i))ᶜ
  let C (d:Faces F) := closure (face F d)∩X
  have hface (d:Faces F) : face F d⊆C d := by
    intro z hz
    refine ⟨subset_closure hz,?_⟩
    intro hh
    obtain ⟨i,-,hi⟩ := mem_iUnion₂.mp hh
    exact hz.1 (mem_iUnion.mpr ⟨i,hi⟩)
  have hcover : (⋃d,C d)=X := by
    apply Subset.antisymm (iUnion_subset fun _=>inter_subset_right)
    intro z hz
    obtain ⟨d,hd⟩ := facial_closures_cover F hF Q hQ z
    exact mem_iUnion.mpr ⟨d,hd,hz⟩
  change IsPreconnected X
  rw [←hcover]
  apply CannonClosedCover.union_preconnected (dualGraph F E) hdual C
    (fun d=>(component_region_connected _ d).isPreconnected.subset_closure (hface d) inter_subset_left)
    (fun d=>(face_nonempty F d).mono (hface d))
  rintro a b ⟨hab,i,hi,ha,hb⟩
  let t : I := ⟨1/2,by constructor <;> norm_num⟩
  have ht₀ : 0<t := by change (0:ℝ)<1/2; norm_num
  have ht₁ : t<1 := by change (1/2:ℝ)<1; norm_num
  have hzX : F i t∈X := by
    intro hh
    obtain ⟨j,hj,s,hs⟩ := mem_iUnion₂.mp hh
    have hij : i≠j := fun h=>hj (h ▸ hi)
    rcases ((hF hij).1 t s hs.symm).1 with h|h
    · exact (ne_of_gt ht₀) h
    · exact (ne_of_lt ht₁) h
  exact ⟨F i t,⟨region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe ha (mem_range_self t),hzX⟩,
    region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hb (mem_range_self t),hzX⟩
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Finite ι]

theorem nonseparating_isAcyclic (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (E : Set ι) (hC : IsPreconnected ((⋃ i∈E,range (F i))ᶜ : Set ℂ)) :
    (edgeGraph F E).IsAcyclic := by
  intro x p hp
  obtain ⟨a,b,h₀,h₁,hint,he⟩ := simple_cycle_arcs F hF p hp
  have hs : range a∪range b⊆⋃ i∈E,range (F i) := by
    rw [he]; exact walkCarrier_edgeUnion F hF p
  have hK : (⋃ i∈E,range (F i))⊆⋃ q∈Q,segment ℝ q.1 q.2 :=
    iUnion₂_subset fun i _=>hQ i
  have hd : Dense ((⋃ i∈E,range (F i))ᶜ : Set ℂ) :=
    (complex_finite_segments_compl_dense Q).mono (compl_subset_compl.mpr hK)
  have hc : IsPreconnected ((range a∪range b)ᶜ : Set ℂ) :=
    hC.subset_closure (compl_subset_compl.mpr hs) (fun z _=>hd z)
  obtain ⟨l,hl⟩ := tame_pair_jordan a b h₀ h₁ hint Q
    (subset_union_left.trans (hs.trans hK)) (subset_union_right.trans (hs.trans hK))
  let _ : PreconnectedSpace ((range a∪range b)ᶜ : Set ℂ) :=
    isPreconnected_iff_preconnectedSpace.mp hc
  have hh : l true=l false := Subsingleton.elim _ _
  exact Bool.noConfusion (l.injective hh)
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
