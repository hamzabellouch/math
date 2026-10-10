import Mathlib
import OAI.Geometry.Cannon.PlanarGraphs.PlanarBounds
import OAI.Geometry.Cannon.PlaneTopology.RetainedFacesSurplus
import OAI.Geometry.Cannon.PlaneTopology.VertexLinkOrder
import OAI.Geometry.Cannon.CirclePacking.OrientedArea

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPlanarEuler CannonPackingGeometry

variable {ι  :  Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem metric_star_flat (F  :  ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (aa bb : ι → Faces F) (hab : ∀i,aa i≠bb i)
    (haa : ∀i,i∈regionEdges F ConnectedComponents.mk (aa i))
    (hbb : ∀i,i∈regionEdges F ConnectedComponents.mk (bb i))
    (r : ℂ → ℝ) (hr : ∀q,0<r q) (c : Faces F → ℂ → ℂ)
    (hc : ∀d,∀u∈faceVertices F d,∀v∈faceVertices F d,u≠v  →  dist (c d u) (c d v)=r u+r v)
    (K : ι → (ℂ ≃ᵢ ℂ))
    (hfold : ∀j,Folds (K j) (c (aa j)) (c (bb j)) (faceVertices F (aa j)) (faceVertices F (bb j)) (F j 0) (F j 1))
    {q : ℂ} (hq : Vertex F q) [Fintype (IncidentFaces F q)]
    (α : IncidentFaces F q → ℝ) (hα : ∀d,α d∈Ioo (0 : ℝ) Real.pi)
    (hs : ∑d,α d=2*Real.pi)
    (hcos : ∀d : IncidentFaces F q,∀u∈faceVertices F d.val,∀v∈faceVertices F d.val,
      q≠u  →  q≠v  →  u≠v  →
      2*(r q+r u)*(r q+r v)*Real.cos (α d)=(r q+r u)^2+(r q+r v)^2-(r u+r v)^2)  :
    ∃ t : Faces F → (ℂ ≃ᵢ ℂ),∀j,q∈range (F j)  →  K j*t (aa j)=t (bb j) := by
  classical
  let _  :  LocallyConnectedSpace ((⋃ i,range (F i))ᶜ  :  Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _  :  DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ  :  Set ℂ)) := inferInstance
  obtain ⟨n,hn,e,a,hn2,hei,hen⟩ := vertexLink_order F hF Q hQ hK hq
  let nx:=CannonCycleOrder.next hn
  have hnxi (i : Fin n) : nx i≠i := CannonCycleOrder.next_ne hn hn2 i
  have exist_w (i : Fin n) : ∃w,Spans (F (e i).val) q w := vertex_spans F hF hq (e i).property
  choose w hw using exist_w
  have hwinj : Function.Injective w := by
    intro i j hij
    have hh:=spans_edge_unique F hF (hw i) (hij ▸ hw j)
    exact e.injective (Subtype.ext hh)
  have hww (i : Fin n) : w i≠w (nx i) := fun hh=>hnxi i (hwinj hh).symm
  have hm (i : Fin n) : q∈faceVertices F (a i).val ∧ w i∈faceVertices F (a i).val ∧ w (nx i)∈faceVertices F (a i).val := by
    refine ⟨(mem_faceVertices F _ _).mpr ⟨hq,(a i).property⟩,?_,?_⟩
    · exact (mem_faceVertices F _ _).mpr ⟨(hw i).vertex_right,
        region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe (hei i) (hw i).mem_right⟩
    · exact (mem_faceVertices F _ _).mpr ⟨(hw (nx i)).vertex_right,
        region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe (hen i) (hw (nx i)).mem_right⟩
  have hget (i : Fin n)  :  ∃J : ℂ ≃ᵢ ℂ,
      Folds J (c (a i).val) (c (a (nx i)).val)
        (faceVertices F (a i).val) (faceVertices F (a (nx i)).val) q (w (nx i)) ∧
      ((J=K (e (nx i)).val ∧ aa (e (nx i)).val=(a i).val ∧ bb (e (nx i)).val=(a (nx i)).val) ∨
       (J=(K (e (nx i)).val).symm ∧ bb (e (nx i)).val=(a i).val ∧ aa (e (nx i)).val=(a (nx i)).val)) := by
    let j := (e (nx i)).val
    have haf  :  (a i).val≠(a (nx i)).val := fun hh=>hnxi i (a.injective (Subtype.ext hh)).symm
    have hpa := edge_face_unique_two F hF Q hQ j haf (hen i) (hei (nx i)) (haa j)
    have hpb := edge_face_unique_two F hF Q hQ j haf (hen i) (hei (nx i)) (hbb j)
    have hfo  :  Folds (K j) (c (aa j)) (c (bb j)) (faceVertices F (aa j)) (faceVertices F (bb j)) q (w (nx i)) := by
      have hsp : Spans (F j) q (w (nx i)) := hw (nx i)
      rcases hsp with ⟨h0,h1⟩|⟨h1,h0⟩
      · simpa only [←h0,←h1] using hfold j
      · simpa only [←h0,←h1] using (hfold j).swap
    rcases hpa with hpa|hpa <;> rcases hpb with hpb|hpb
    · exact ((hab j) (hpa.trans hpb.symm)).elim
    · exact ⟨K j,by simpa only [hpa,hpb] using hfo,Or.inl ⟨rfl,hpa,hpb⟩⟩
    · exact ⟨(K j).symm,by simpa only [hpa,hpb] using hfo.symm,Or.inr ⟨rfl,hpb,hpa⟩⟩
    · exact ((hab j) (hpa.trans hpb.symm)).elim
  choose J hJ hpair using hget
  obtain ⟨t,ht⟩ := finite_cyclic_folded_frames hn
    (fun i=>r q+r (w i)) (fun i=>α (a i)) (fun i=>r (w i)+r (w (nx i)))
    (fun i=>add_pos (hr _) (hr _)) (fun i=>add_pos (hr _) (hr _)) (fun i=>hα (a i))
    ((a.sum_comp α).trans hs)
    (fun i=>hcos (a i) _ (hm i).2.1 _ (hm i).2.2 (hw i).ne (hw (nx i)).ne (hww i))
    (fun i=>c (a i).val q) (fun i=>c (a i).val (w i)) (fun i=>c (a i).val (w (nx i)))
    (fun i=>hc _ _ (hm i).1 _ (hm i).2.1 (hw i).ne)
    (fun i=>hc _ _ (hm i).1 _ (hm i).2.2 (hw (nx i)).ne)
    (fun i=>hc _ _ (hm i).2.1 _ (hm i).2.2 (hww i)) J
    (fun i=>(hJ i).1) (fun i=>(hJ i).2.1)
    (fun i=>(hJ i).2.2 _ (hm i).2.1 (hw i).ne.symm (hww i) _
      (hm (nx i)).2.2 (hw (nx (nx i))).ne.symm (hww (nx i)).symm)
  let T : Faces F → (ℂ ≃ᵢ ℂ) := fun d=>if h : q∈closure (face F d) then t (a.symm ⟨d,h⟩) else 1
  have hT (i : Fin n) : T (a i).val=t i := by
    dsimp only [T]
    have hp : q∈closure (face F (a i).val) := (a i).property
    rw [dite_eq_left hp]
    simp
  refine ⟨T,fun j hj=>?_⟩
  obtain ⟨i,hi⟩ := CannonCycleOrder.next_surjective hn (e.symm ⟨j,hj⟩)
  have hei'  :  (e (nx i)).val=j := by
    change (e (CannonCycleOrder.next hn i)).val=j
    rw [hi]; simp
  have hti := ht i
  rcases hpair i with ⟨hJ,hA,hB⟩|⟨hJ,hB,hA⟩
  · rw [hei'] at hJ hA hB
    rw [hA,hB,hT,hT]
    simpa only [hJ] using hti
  · rw [hei'] at hJ hA hB
    rw [hA,hB,hT,hT]
    have hh:=congrArg (fun z=>(K j)*z) hti
    rw [hJ] at hh
    change K j * t (nx i) = _
    have hc : K j * (K j).symm = 1 := by ext z; exact (K j).apply_symm_apply z
    simpa only [←mul_assoc,hc,one_mul] using hh.symm
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonFaceIncidence CannonPolygonal CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma facial_vertex_has_edge (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (d : Faces F) {q : ℂ} (hq : q∈faceVertices F d) :
    ∃ i∈regionEdges F ConnectedComponents.mk d,F i 0=q ∨ F i 1=q := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  have hq' := (mem_faceVertices F d q).mp hq
  have hcl := tame_region_closure F hF Q hQ ConnectedComponents.continuous_coe d
  change closure (face F d)=face F d∪⋃ e∈regionEdges F ConnectedComponents.mk d,range (F e) at hcl
  have hx := hq'.2
  rw [hcl] at hx
  have hs := hx.resolve_left (fun hh=>hh.1 (vertex_mem_support F hq'.1))
  obtain ⟨i,hi,t,ht⟩ := mem_iUnion₂.mp hs
  refine ⟨i,hi,?_⟩
  rcases vertex_parameter F hF i (ht.symm ▸ hq'.1) with h|h
  · exact Or.inl (h ▸ ht)
  · exact Or.inr (h ▸ ht)

omit [Nonempty ι] in
lemma facial_edge_ends (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (d : Faces F) {i : ι} (hi : i∈regionEdges F ConnectedComponents.mk d) :
    F i 0∈faceVertices F d ∧ F i 1∈faceVertices F d := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  constructor
  · exact (mem_faceVertices F d _).mpr ⟨⟨i,Or.inl rfl⟩,
      region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hi (mem_range_self 0)⟩
  · exact (mem_faceVertices F d _).mpr ⟨⟨i,Or.inr rfl⟩,
      region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hi (mem_range_self 1)⟩

theorem proper_facial_bound (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hthree : ∀ d : Faces F,3≤Nat.card (regionEdges F ConnectedComponents.mk d))
    (T : Finset ℂ) (hproper : ¬vertices F Finset.univ⊆T)
    (hB : ∃ d : Faces F,faceVertices F d⊆T) :
    Nat.card {d : Faces F | faceVertices F d⊆T}+5≤2*T.card := by
  classical
  let S : Finset ι := Finset.univ.filter (fun i=>F i 0∈T ∧ F i 1∈T)
  have heq (d : Faces F) : regionEdges F ConnectedComponents.mk d⊆(S:Set ι) ↔ faceVertices F d⊆T := by
    constructor
    · intro hs q hq
      obtain ⟨i,hi,h⟩ := facial_vertex_has_edge F hF Q hQ d hq
      have ht := (Finset.mem_filter.mp (hs hi)).2
      exact h.elim (fun h=>h ▸ ht.1) (fun h=>h ▸ ht.2)
    · intro ht i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨ht (facial_edge_ends F hF Q hQ d hi).1,ht (facial_edge_ends F hF Q hQ d hi).2⟩⟩
  obtain ⟨d,hd⟩ := hB
  have hS3 : 3≤S.card := by
    have hh := Nat.card_mono (Set.toFinite (S:Set ι)) ((heq d).mpr hd)
    simpa only [Nat.card_coe_set_eq,Set.ncard_coe_finset] using (hthree d).trans hh
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hSp : S≠Finset.univ := by
    intro he
    apply hproper
    intro q hq
    obtain ⟨i,_,hq⟩ := (mem_vertices F Finset.univ q).mp hq
    have hi : i∈S := he ▸ Finset.mem_univ i
    have ht := (Finset.mem_filter.mp hi).2
    exact hq.elim (fun h=>h ▸ ht.1) (fun h=>h ▸ ht.2)
  let _ : Nonempty S := hS.to_subtype
  let H : S → Arc ℂ := fun i=>F i.val
  have hHV : vertices H Finset.univ⊆T := by
    intro q hq
    obtain ⟨i,_,hq⟩ := (mem_vertices H Finset.univ q).mp hq
    have ht := (Finset.mem_filter.mp i.property).2
    exact hq.elim (fun h=>h ▸ ht.1) (fun h=>h ▸ ht.2)
  have hV := Finset.card_le_card hHV
  have hp := (planar_bounds H (fun _ _ hn=>hF (fun he=>hn (Subtype.ext he))) Q
    (fun i=>hQ i.val) (by simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hS3)).2
  have hr := retained_faces_surplus F hF Q hQ S hS hSp
  have hset : {d : Faces F | regionEdges F ConnectedComponents.mk d⊆(S:Set ι)}=
      {d : Faces F | faceVertices F d⊆T} := Set.ext heq
  rw [hset] at hr
  change Nat.card {d : Faces F | faceVertices F d⊆T}+1≤Nat.card (Faces H) at hr
  omega
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
