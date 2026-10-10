import Mathlib
import OAI.Geometry.Cannon.PlanarGraphs.Support
import OAI.Geometry.Cannon.PlanarGraphs.InteriorUnion

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
lemma facial_closures_cover (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2) :
    ∀ x : ℂ,∃ d : Faces F,x∈closure (face F d) := by
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  have hd : Dense ((⋃ i,range (F i))ᶜ : Set ℂ) := (complex_finite_segments_compl_dense Q).mono (by
    intro x hx hh
    obtain ⟨i,hi⟩ := mem_iUnion.mp hh
    exact hx (hQ i hi))
  have hC : IsClosed (⋃ d : Faces F,closure (face F d)) :=
    isClosed_iUnion_of_finite fun _ => isClosed_closure
  have hsub : (⋃ i,range (F i))ᶜ⊆⋃ d : Faces F,closure (face F d) := by
    intro x hx
    refine mem_iUnion.mpr ⟨ConnectedComponents.mk ⟨x,hx⟩,subset_closure ?_⟩
    exact ⟨hx,rfl⟩
  intro x
  exact mem_iUnion.mp ((closure_minimal hsub hC) (hd x))

omit [DecidableEq ι] [Nonempty ι] in
theorem common_vertex_at (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hcorner : ∀ d : Faces F,(faceVertices F d).Nonempty) (x : ℂ) :
    ∃ v∈vertices F Finset.univ,∀ d : Faces F,x∈closure (face F d) → v∈faceVertices F d := by
  classical
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  by_cases hxv : Vertex F x
  · refine ⟨x,?_,fun d hd=>(mem_faceVertices F d x).mpr ⟨hxv,hd⟩⟩
    obtain ⟨i,hi⟩ := hxv
    exact (mem_vertices F Finset.univ x).mpr ⟨i,Finset.mem_univ _,hi⟩
  by_cases hxK : x∈⋃ i,range (F i)
  · obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hxK
    have ht₀ : 0<t := by
      apply lt_of_le_of_ne (nonneg t)
      intro he
      exact hxv ⟨i,Or.inl (congrArg (F i) (show (0:I)=t from Subtype.ext he))⟩
    have ht₁ : t<1 := by
      apply lt_of_le_of_ne (le_one t)
      intro he
      exact hxv ⟨i,Or.inr (congrArg (F i) (show (1:I)=t from Subtype.ext he.symm))⟩
    refine ⟨F i 0,(mem_vertices F Finset.univ (F i 0)).mpr ⟨i,Finset.mem_univ _,Or.inl rfl⟩,?_⟩
    intro d hd
    apply (mem_faceVertices F d _).mpr
    refine ⟨⟨i,Or.inl rfl⟩,?_⟩
    exact region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe
      (show i∈regionEdges F ConnectedComponents.mk d from ⟨t,ht₀,ht₁,hd⟩) (mem_range_self 0)
  · let d := ConnectedComponents.mk (⟨x,hxK⟩ : ((⋃ i,range (F i))ᶜ : Set ℂ))
    obtain ⟨v,hv⟩ := hcorner d
    have hvV := ((mem_faceVertices F d v).mp hv).1
    obtain ⟨i,hi⟩ := hvV
    refine ⟨v,(mem_vertices F Finset.univ v).mpr ⟨i,Finset.mem_univ _,hi⟩,?_⟩
    intro c hxc
    have hcl := tame_region_closure F hF Q hQ ConnectedComponents.continuous_coe c
    change closure (face F c)=face F c∪_ at hcl
    rw [hcl] at hxc
    have hxface : x∈face F c := by
      rcases hxc with h|h
      · exact h
      · obtain ⟨j,-,hj⟩ := mem_iUnion₂.mp h
        exact (hxK (mem_iUnion.mpr ⟨j,hj⟩)).elim
    have hc : c=d := hxface.2.symm
    exact hc.symm ▸ hv

def facialStar (F : ι → Arc ℂ) (v : ℂ) : Set ℂ :=
  ⋃ d : Faces F,⋃ (_ : v∈faceVertices F d),closure (face F d)

omit [DecidableEq ι] [Nonempty ι] in
lemma facialStar_closed (F : ι → Arc ℂ) [Finite (Faces F)] (v : ℂ) :
    IsClosed (facialStar F v) :=
  isClosed_iUnion_of_finite fun _ => isClosed_iUnion_of_finite fun _ => isClosed_closure

omit [DecidableEq ι] in
theorem facialStar_interiors_cover (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hcorner : ∀ d : Faces F,(faceVertices F d).Nonempty) :
    ∀ x : ℂ,∃ v∈vertices F Finset.univ,x∈interior (facialStar F v) := by
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  intro x
  obtain ⟨v,hv,hvd⟩ := common_vertex_at F hF Q hQ hcorner x
  exact ⟨v,hv,CannonFacialStars.interior_union_at _ (fun _=>isClosed_closure)
    (facial_closures_cover F hF Q hQ) {d | v∈faceVertices F d} hvd⟩
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
