import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.ClosedInside
import OAI.Geometry.Cannon.Topology.NoTripleClosedBalls

namespace OAI

section
section
section
noncomputable section
namespace CannonTriangleWinding
open Set Metric Topology

lemma closedInside_zero_segment {a b c p : ℂ} (h : 0<area a b c)
    (hp : ClosedInside a b c p) (hz : area a b p=0) : p∈segment ℝ a b := by
  refine ⟨area b c p/area a b c,area c a p/area a b c,
    div_nonneg hp.2.1 h.le,div_nonneg hp.2.2 h.le,?_,?_⟩
  · rw [←add_div]
    have hs:=area_sum a b c p
    have he : area b c p+area c a p=area a b c := by linarith
    rw [he,div_self h.ne']
  · have H:=area_barycentric a b c p h.ne'
    simpa only [hz,zero_div,zero_smul,add_zero] using H

lemma frontier_hull_segments {a b c : ℂ} (h : 0<area a b c) :
    frontier (convexHull ℝ ({a,b,c}:Set ℂ))⊆
      segment ℝ a b∪segment ℝ b c∪segment ℝ c a := by
  intro p hp
  have hclosed : IsClosed (convexHull ℝ ({a,b,c}:Set ℂ)) :=
    (Set.toFinite ({a,b,c}:Set ℂ)).isCompact_convexHull ℝ |>.isClosed
  have hin : ClosedInside a b c p := by
    have H:=hclosed.closure_eq ▸ hp.1
    rw [convexHull_eq_closedInside h] at H
    exact H
  have hout : ¬ Inside a b c p := by
    simpa only [convexHull_interior h,mem_ofPred_eq] using hp.2
  have hz : area a b p=0 ∨ area b c p=0 ∨ area c a p=0 := by
    by_contra H
    push Not at H
    exact hout ⟨lt_of_le_of_ne hin.1 (Ne.symm H.1),
      lt_of_le_of_ne hin.2.1 (Ne.symm H.2.1),lt_of_le_of_ne hin.2.2 (Ne.symm H.2.2)⟩
  rcases hz with hz|hz|hz
  · exact Or.inl (Or.inl (closedInside_zero_segment h hin hz))
  · exact Or.inl (Or.inr (closedInside_zero_segment (by rwa [area_cyclic])
      ⟨hin.2.1,hin.2.2,hin.1⟩ hz))
  · exact Or.inr (closedInside_zero_segment (by rwa [area_cyclic,area_cyclic])
      ⟨hin.2.2,hin.1,hin.2.1⟩ hz)

lemma hull_inter_frontier {a b c u v w p : ℂ}
    (h : 0<area a b c) (hk : 0<area u v w)
    (hdis : Disjoint (interior (convexHull ℝ ({a,b,c}:Set ℂ)))
      (interior (convexHull ℝ ({u,v,w}:Set ℂ))))
    (hp : p∈convexHull ℝ ({a,b,c}:Set ℂ))
    (hq : p∈convexHull ℝ ({u,v,w}:Set ℂ)) :
    p∈frontier (convexHull ℝ ({a,b,c}:Set ℂ)) ∧
      p∈frontier (convexHull ℝ ({u,v,w}:Set ℂ)) := by
  have hc1 : closure (interior (convexHull ℝ ({a,b,c}:Set ℂ)))=convexHull ℝ ({a,b,c}:Set ℂ) := by
    rw [convexHull_interior h,convexHull_closure_inside h]
  have hc2 : closure (interior (convexHull ℝ ({u,v,w}:Set ℂ)))=convexHull ℝ ({u,v,w}:Set ℂ) := by
    rw [convexHull_interior hk,convexHull_closure_inside hk]
  have ha : p∉interior (convexHull ℝ ({a,b,c}:Set ℂ)) := by
    have H:=hdis.symm.closure_left isOpen_interior
    rw [hc2] at H
    exact fun hh=>Set.disjoint_left.mp H hq hh
  have hb : p∉interior (convexHull ℝ ({u,v,w}:Set ℂ)) := by
    have H:=hdis.closure_left isOpen_interior
    rw [hc1] at H
    exact fun hh=>Set.disjoint_left.mp H hp hh
  exact ⟨⟨subset_closure hp,ha⟩,⟨subset_closure hq,hb⟩⟩
end CannonTriangleWinding

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {d e : Faces F}

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma FacialCycle.frontier_edges (C : FacialCycle F d) (z : ℂ → ℂ)
    (hpos : 0<area (z C.a) (z C.b) (z C.c)) {p : ℂ}
    (hp : p∈frontier (faceHull F z d)) :
    ∃ u∈faceVertices F d,∃ v∈faceVertices F d,u≠v ∧ p∈segment ℝ (z u) (z v) := by
  rw [C.hull_eq] at hp
  rcases frontier_hull_segments hpos hp with (hp|hp)|hp
  · exact ⟨C.a,C.mem_a,C.b,C.mem_b,C.ab,hp⟩
  · exact ⟨C.b,C.mem_b,C.c,C.mem_c,C.bc,hp⟩
  · exact ⟨C.c,C.mem_c,C.a,C.mem_a,C.ac.symm,hp⟩

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma FacialCycle.common_vertex_of_frontier_inter (C : FacialCycle F d) (E : FacialCycle F e)
    (z : ℂ → ℂ) (r : ℂ → ℝ) (hr : ∀ v,0<r v)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=r (F i 0)+r (F i 1))
    (hdis : ∀ u,Vertex F u → ∀ v,Vertex F v → u≠v → r u+r v≤dist (z u) (z v))
    (hC : 0<area (z C.a) (z C.b) (z C.c))
    (hE : 0<area (z E.a) (z E.b) (z E.c))
    (hp : (frontier (faceHull F z d)∩frontier (faceHull F z e)).Nonempty) :
    ∃ v,v∈faceVertices F d ∧ v∈faceVertices F e := by
  classical
  by_contra hn
  have hne (u : ℂ) (hu : u∈faceVertices F d) (v : ℂ) (hv : v∈faceVertices F e) : u≠v := by
    intro H
    subst v
    exact hn ⟨u,hu,hv⟩
  obtain ⟨p,hpd,hpe⟩:=hp
  obtain ⟨u,hu,v,hv,huv,hp⟩:=C.frontier_edges z hC hpd
  obtain ⟨w,hw,t,ht,hwt,hq⟩:=E.frontier_edges z hE hpe
  have hvV {d : Faces F} {v : ℂ} (hv : v∈faceVertices F d) : Vertex F v :=
    ((mem_faceVertices F d v).mp hv).1
  have H:=CannonTangentSegments.disjoint_edges (hr u) (hr v) (hr w) (hr t)
    (C.developed_length hu hv huv z r hlen) (E.developed_length hw ht hwt z r hlen)
    (hdis u (hvV hu) w (hvV hw) (hne u hu w hw))
    (hdis u (hvV hu) t (hvV ht) (hne u hu t ht))
    (hdis v (hvV hv) w (hvV hw) (hne v hv w hw))
    (hdis v (hvV hv) t (hvV ht) (hne v hv t ht))
  exact Set.disjoint_left.mp H hp hq

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma FacialCycle.common_vertex_of_hull_inter (C : FacialCycle F d) (E : FacialCycle F e)
    (z : ℂ → ℂ) (r : ℂ → ℝ) (hr : ∀ v,0<r v)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=r (F i 0)+r (F i 1))
    (hdis : ∀ u,Vertex F u → ∀ v,Vertex F v → u≠v → r u+r v≤dist (z u) (z v))
    (hC : 0<area (z C.a) (z C.b) (z C.c))
    (hE : 0<area (z E.a) (z E.b) (z E.c))
    (hI : Disjoint (interior (faceHull F z d)) (interior (faceHull F z e)))
    (hp : (faceHull F z d∩faceHull F z e).Nonempty) :
    ∃ v,v∈faceVertices F d ∧ v∈faceVertices F e := by
  apply C.common_vertex_of_frontier_inter E z r hr hlen hdis hC hE
  obtain ⟨p,hpd,hpe⟩:=hp
  refine ⟨p,?_⟩
  simp only [C.hull_eq,E.hull_eq] at hI hpd hpe ⊢
  exact hull_inter_frontier hC hE hI hpd hpe
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}
omit [DecidableEq ι] [Fintype (Faces F)] in
lemma vertex_inner_face
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    {v : ℂ} (hvV : Vertex F v) : ∃ d:Faces F,d≠out ∧ v∈faceVertices F d := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  obtain ⟨i,hi⟩ := hvV
  have hv : v∈range (F i) := hi.elim (fun h=>h ▸ ⟨0,rfl⟩) (fun h=>h ▸ ⟨1,rfl⟩)
  obtain ⟨a,b,hab,ha,hb⟩ := noncut_edge_two_faces F hF Q hQ hK i
  have mem (d : Faces F) (hd : i∈regionEdges F ConnectedComponents.mk d) : v∈faceVertices F d :=
    (mem_faceVertices F _ _).mpr ⟨⟨i,hi⟩,region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hd hv⟩
  by_cases hao : a=out
  · exact ⟨b,fun h=>hab (hao.trans h.symm),mem b hb⟩
  · exact ⟨a,hao,mem a ha⟩

theorem DevelopedFaces.hull_geometry (B : DevelopedFaces F out)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (hthree : ∀ d,(faceVertices F d).card=3)
    (z : ℂ → ℂ) (hz : ∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q) :
    (∀ d : Faces F,∃ C : FacialCycle F d,0<area (z C.a) (z C.b) (z C.c)) ∧
    (∀ d e : Faces F,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull F z d)) (interior (faceHull F z e))) ∧
    (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out := by
  classical
  obtain ⟨w,C,O,hw,hlen,hpos,ho,hchain,hdis⟩:=B.univalent_triangles hF Q hQ hK hthree
  have heq (v : ℂ) (hv : Vertex F v) : z v=w v := by
    obtain ⟨d,hd,hm⟩:=vertex_inner_face hF Q hQ hK hv
    exact (hz d hd v hm).trans (hw d hd v hm).symm
  have heqV (d : Faces F) (v : ℂ) (hv : v∈faceVertices F d) : z v=w v:=
    heq v ((mem_faceVertices F d v).mp hv).1
  have hhull (d : Faces F) : faceHull F z d=faceHull F w d := by
    unfold faceHull
    congr 1
    exact Set.image_congr (fun x hx=>heqV d x hx)
  have hcycle (d : Faces F) (C : FacialCycle F d) :
      area (z C.a) (z C.b) (z C.c)=area (w C.a) (w C.b) (w C.c) := by
    rw [heqV d C.a C.mem_a,heqV d C.b C.mem_b,heqV d C.c C.mem_c]
  refine ⟨?_,?_,?_⟩
  · intro d
    by_cases hd : d=out
    · subst d
      exact ⟨O,by rw [hcycle]; exact ho⟩
    · exact ⟨C ⟨d,hd⟩,by rw [hcycle]; exact hpos ⟨d,hd⟩⟩
  · intro d e hd he hde
    rw [hhull,hhull,(C ⟨d,hd⟩).hull_eq,(C ⟨e,he⟩).hull_eq,
      convexHull_interior (hpos ⟨d,hd⟩),convexHull_interior (hpos ⟨e,he⟩)]
    exact hdis (show (⟨d,hd⟩:{d : Faces F // d≠out})≠⟨e,he⟩ from fun h=>hde (congrArg Subtype.val h))
  · simp_rw [hhull]
    have H:=triangle_closures_fill (fun d=>w (C d).a) (fun d=>w (C d).b) (fun d=>w (C d).c)
      (w O.a) (w O.b) (w O.c) hpos ho (hchain ℤ)
    simp only [convexHull_closure_inside (hpos _),convexHull_closure_inside ho] at H
    simp_rw [(C _).hull_eq,O.hull_eq]
    exact H
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence

variable {ι X Y : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [TopologicalSpace X] [TopologicalSpace Y]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma compactifiedFace_mapsTo (F : ι → Arc ℂ) (e : ℂ → X) (f : C(X,Y))
    (d : Faces F) (U : Set Y) (hU : IsClosed U)
    (hf : MapsTo (f ∘ e) (closure (face F d)) U) :
    MapsTo f (compactifiedFace F e d) U := by
  apply Set.MapsTo.closure_left (hc:=f.continuous) (ht:=hU)
  rintro _ ⟨x,hx,rfl⟩
  exact hf (subset_closure hx)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma compactifiedFace_dist_bound {X : Type*} [PseudoMetricSpace X]
    (F : ι → Arc ℂ) (e : ℂ → X) (d : Faces F) (R : ℝ)
    (hR : ∀ z∈closure (face F d),∀ w∈closure (face F d),dist (e z) (e w)≤R) :
    ∀ x∈compactifiedFace F e d,∀ y∈compactifiedFace F e d,dist x y≤R := by
  intro x hx y hy
  have H : dist x y∈closure (Iic R) :=
    map_mem_closure₂ continuous_dist hx hy (by
      rintro _ ⟨z,hz,rfl⟩ _ ⟨w,hw,rfl⟩
      exact hR z (subset_closure hz) w (subset_closure hw))
  simpa only [closure_Iic,mem_Iic] using H
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
