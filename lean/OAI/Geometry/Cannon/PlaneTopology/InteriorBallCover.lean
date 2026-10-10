import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.InnerFlux
import OAI.Geometry.Cannon.CirclePacking.Det

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}
attribute [local instance] Classical.propDecidable

theorem DevelopedFaces.interior_ball_cover (B : DevelopedFaces F out)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (z : ℂ → ℂ) (hz : ∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q)
    {q : ℂ} (hq : Vertex F q) (hqo : q∉faceVertices F out)
    {p : ℂ} (hp : dist (z q) p<B.radius q)
    (hgen : ∀ i,orientedArea (z (F i 0)) (z (F i 1)) p≠0) :
    ∃ d : Faces F,d≠out ∧ ∃ u v : ℂ,
      q∈faceVertices F d ∧ u∈faceVertices F d ∧ v∈faceVertices F d ∧
      q≠u ∧ q≠v ∧ u≠v ∧ TriInterior (z q) (z u) (z v) p := by
  classical
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  have hinner (d : IncidentFaces F q) : d.val≠out := by
    intro hd
    exact hqo ((mem_faceVertices F _ _).mpr ⟨hq,hd ▸ d.property⟩)
  have hmem (d : IncidentFaces F q) : q∈faceVertices F d.val := (mem_faceVertices F _ _).mpr ⟨hq,d.property⟩
  have hsum : (∑ d : IncidentFaces F q,B.angle d.val q)=2*Real.pi := by
    have hh := Fintype.sum_subtype_add_sum_subtype (fun d : Faces F=>q∈closure (face F d)) (fun d=>B.angle d q)
    have hzz : (∑ d : {d : Faces F // ¬q∈closure (face F d)},B.angle d.val q)=0 := by
      apply Finset.sum_eq_zero
      intro d hd
      exact B.angle_zero _ _ (fun h=>d.property ((mem_faceVertices F _ _).mp h).2)
    rw [hzz,add_zero,B.angle_sum q hq,ite_eq_right hqo] at hh
    exact hh
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
    refine ⟨hmem (a i),?_,?_⟩
    · exact (mem_faceVertices F _ _).mpr ⟨(hw i).vertex_right,
        region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe (hei i) (hw i).mem_right⟩
    · exact (mem_faceVertices F _ _).mpr ⟨(hw (nx i)).vertex_right,
        region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe (hen i) (hw (nx i)).mem_right⟩
  have len (d : IncidentFaces F q) {u v : ℂ}
      (hu : u∈faceVertices F d.val) (hv : v∈faceVertices F d.val) (huv : u≠v) :
      dist (z u) (z v)=B.radius u+B.radius v := by
    rw [hz d.val (hinner d) u hu,hz d.val (hinner d) v hv]
    exact B.lengths d.val u hu v hv huv
  have hop (i : Fin n) : orientedArea (z q) (z (w (nx i))) (z (w i))*
      orientedArea (z q) (z (w (nx i))) (z (w (nx (nx i))))<0 := by
    let j := (e (nx i)).val
    have had : (a i).val≠(a (nx i)).val := fun hh=>hnxi i (a.injective (Subtype.ext hh)).symm
    have hq0 : q∈faceVertices F (a (nx i)).val := (hm (nx i)).1
    have hw0 : w (nx i)∈faceVertices F (a (nx i)).val := (hm (nx i)).2.1
    have hsp : Spans (F j) q (w (nx i)) := hw (nx i)
    rcases hsp with ⟨he0,he1⟩|⟨he0,he1⟩
    · have H := B.opposite j (a i).val (a (nx i)).val had (hinner _) (hinner _) (hen i) (hei (nx i))
        (w i) (hm i).2.1 (by rw [he0]; exact (hw i).ne.symm) (by rw [he1]; exact hww i)
        (w (nx (nx i))) (hm (nx i)).2.2 (by rw [he0]; exact (hw (nx (nx i))).ne.symm)
        (by rw [he1]; exact (hww (nx i)).symm)
      rw [he0,he1,←hz _ (hinner _) _ hq0,←hz _ (hinner _) _ hw0,
        ←hz _ (hinner _) _ (hm i).2.1,←hz _ (hinner _) _ (hm (nx i)).2.2] at H
      exact H
    · have H := B.opposite j (a i).val (a (nx i)).val had (hinner _) (hinner _) (hen i) (hei (nx i))
        (w i) (hm i).2.1 (by rw [he1]; exact hww i) (by rw [he0]; exact (hw i).ne.symm)
        (w (nx (nx i))) (hm (nx i)).2.2 (by rw [he1]; exact (hww (nx i)).symm)
        (by rw [he0]; exact (hw (nx (nx i))).ne.symm)
      rw [he0,he1,←hz _ (hinner _) _ hq0,←hz _ (hinner _) _ hw0,
        ←hz _ (hinner _) _ (hm i).2.1,←hz _ (hinner _) _ (hm (nx i)).2.2] at H
      have hs : orientedArea (z (w (nx i))) (z q) (z (w i))*
          orientedArea (z (w (nx i))) (z q) (z (w (nx (nx i))))=
          orientedArea (z q) (z (w (nx i))) (z (w i))*
          orientedArea (z q) (z (w (nx i))) (z (w (nx (nx i)))) := by
        rw [orientedArea_swap_first (z (w (nx i))) (z q) (z (w i)),
          orientedArea_swap_first (z (w (nx i))) (z q) (z (w (nx (nx i)))),neg_mul_neg]
      rw [hs] at H
      exact H
  have hgp (i : Fin n) : orientedArea (z q) (z (w i)) p≠0 := by
    have H := hgen (e i).val
    rcases hw i with ⟨h0,h1⟩|⟨h1,h0⟩
    · simpa only [h0,h1] using H
    · rw [h0,h1,orientedArea_swap_first] at H
      exact neg_ne_zero.mp H
  obtain ⟨i,hi⟩ := finite_star_ball_cover hn (B.radius q) (fun i=>B.radius (w i))
    (fun i=>B.angle (a i).val q) (B.radius_pos q) (fun i=>B.radius_pos _)
    (fun i=>B.angle_pos _ (hinner _) q (hm i).1)
    ((a.sum_comp (fun d=>B.angle d.val q)).trans hsum)
    (fun i=>B.cosine _ (hinner _) q (hm i).1 _ (hm i).2.1 _ (hm i).2.2
      (hw i).ne (hw (nx i)).ne (hww i)) (z q) (fun i=>z (w i))
    (fun i=>len (a i) (hm i).1 (hm i).2.1 (hw i).ne)
    (fun i=>len (a i) (hm i).2.1 (hm i).2.2 (hww i)) hop hp hgp
  exact ⟨(a i).val,hinner _,w i,w (nx i),(hm i).1,(hm i).2.1,(hm i).2.2,
    (hw i).ne,(hw (nx i)).ne,hww i,hi⟩

end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonTriangleWinding
open Set Topology

attribute [local instance] Classical.propDecidable

lemma generic_union_iff {D : Type*} [Fintype D] (a b c : D → ℂ) (u v w p : ℂ)
    (hpos : ∀ d,0<area (a d) (b d) (c d)) (ho : 0<area u v w)
    (hg : ∀ d,Generic (a d) (b d) (c d) p) (hgo : Generic u v w p)
    (hc : ∀ f : ℂ → ℂ → ℤ,(∀ x y,f y x= -f x y) →
      (∑ d : D,(f (a d) (b d)+f (b d) (c d)+f (c d) (a d)))=f u v+f v w+f w u) :
    (∃ d,Inside (a d) (b d) (c d) p) ↔ Inside u v w p := by
  classical
  have H := hc (edgeIndex p) (edgeIndex_swap p)
  simp only [triangle_index (hpos _) (hg _),triangle_index ho hgo] at H
  constructor
  · rintro ⟨d,hd⟩
    have hl : (1:ℤ)≤∑ i,if Inside (a i) (b i) (c i) p then (1:ℤ) else 0 := by
      have hh := Finset.single_le_sum (f:=fun i=>if Inside (a i) (b i) (c i) p then (1:ℤ) else 0)
        (fun i hi=>by split_ifs <;> norm_num) (Finset.mem_univ d)
      simpa only [ite_eq_left hd] using hh
    rw [H] at hl
    by_contra hn
    simp only [ite_eq_right hn] at hl
    norm_num at hl
  · intro hp
    by_contra hn
    push Not at hn
    simp only [ite_eq_right (hn _),Finset.sum_const_zero,ite_eq_left hp] at H
    norm_num at H

lemma closure_eq_of_dense_inter_eq {X : Type*} [TopologicalSpace X]
    {G U V : Set X} (hG : Dense G) (hU : IsOpen U) (hV : IsOpen V) (hUV : G∩U=G∩V) :
    closure U=closure V := by
  apply le_antisymm
  · apply closure_minimal ?_ isClosed_closure
    exact (hG.open_subset_closure_inter hU).trans (by rw [Set.inter_comm U G,hUV]; exact closure_mono inter_subset_right)
  · apply closure_minimal ?_ isClosed_closure
    exact (hG.open_subset_closure_inter hV).trans (by rw [Set.inter_comm V G,←hUV]; exact closure_mono inter_subset_right)

theorem triangle_closures_fill {D : Type*} [Fintype D] (a b c : D → ℂ) (u v w : ℂ)
    (hpos : ∀ d,0<area (a d) (b d) (c d)) (ho : 0<area u v w)
    (hchain : ∀ f : ℂ → ℂ → ℤ,(∀ x y,f y x= -f x y) →
      (∑ d : D,(f (a d) (b d)+f (b d) (c d)+f (c d) (a d)))=f u v+f v w+f w u) :
    (⋃ d,closure {p | Inside (a d) (b d) (c d) p})=closure {p | Inside u v w p} := by
  have hg (d : D) := generic_dense_open (a d) (b d) (c d)
    (area_pos_distinct (hpos d)).1 (area_pos_distinct (hpos d)).2.1 (area_pos_distinct (hpos d)).2.2
  have hgO := generic_dense_open u v w (area_pos_distinct ho).1
    (area_pos_distinct ho).2.1 (area_pos_distinct ho).2.2
  let G := (⋂ d : D,{p | Generic (a d) (b d) (c d) p})∩{p | Generic u v w p}
  have hG : Dense G :=
    (dense_iInter_of_isOpen (fun d=>(hg d).2) (fun d=>(hg d).1)).inter_of_isOpen_right hgO.1 hgO.2
  rw [←closure_iUnion_of_finite]
  apply closure_eq_of_dense_inter_eq hG (isOpen_iUnion fun d=>inside_open _ _ _) (inside_open _ _ _)
  ext p
  change (p∈G ∧ p∈⋃ d,{p | Inside (a d) (b d) (c d) p}) ↔ p∈G ∧ Inside u v w p
  simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
  apply and_congr_right
  intro hp
  exact generic_union_iff a b c u v w p hpos ho (fun d=>mem_iInter.mp hp.1 d) hp.2 hchain

end CannonTriangleWinding

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}
attribute [local instance] Classical.propDecidable

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma FacialCycle.inside_of_interior {d : Faces F} (C : FacialCycle F d) (z : ℂ → ℂ)
    (hpos : 0<CannonTriangleWinding.area (z C.a) (z C.b) (z C.c))
    {q u v p : ℂ} (hq : q∈faceVertices F d) (hu : u∈faceVertices F d) (hv : v∈faceVertices F d)
    (hqu : q≠u) (hqv : q≠v) (huv : u≠v)
    (h : TriInterior (z q) (z u) (z v) p) :
    CannonTriangleWinding.Inside (z C.a) (z C.b) (z C.c) p := by
  classical
  have hV : faceVertices F d={q,u,v} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl|rfl <;> assumption
    · rw [C.vertices]
      simp [C.ab,C.ac,C.bc,hqu,hqv,huv]
  have mem {x : ℂ} (hx : x∈faceVertices F d) : z x∈({z q,z u,z v}:Finset ℂ) := by
    rw [hV] at hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢
    rcases hx with rfl|rfl|rfl <;> simp
  have hd := CannonTriangleWinding.area_pos_distinct hpos
  exact (h.of_vertices (mem C.mem_a) (mem C.mem_b) (mem C.mem_c) hd.1 hd.2.2.symm hd.2.1).inside hpos

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma developed_edges_generic_dense (z : ℂ → ℂ) (r : ℂ → ℝ) (hr : ∀ q,0<r q)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=r (F i 0)+r (F i 1)) :
    Dense (⋂ i : ι,{p | orientedArea (z (F i 0)) (z (F i 1)) p≠0}) := by
  have hne (i : ι) : z (F i 0)≠z (F i 1) := by
    intro h
    have H:=hlen i
    rw [h,dist_self] at H
    linarith [hr (F i 0),hr (F i 1)]
  have hd (i : ι) : Dense {p | orientedArea (z (F i 0)) (z (F i 1)) p≠0} := by
    simp only [←winding_area_eq]
    exact CannonTriangleWinding.dense_ne_of_openMap _ (CannonTriangleWinding.area_openMap (hne i)) 0
  have ho (i : ι) : IsOpen {p | orientedArea (z (F i 0)) (z (F i 1)) p≠0} := by
    apply isOpen_ne_fun _ continuous_const
    unfold orientedArea
    fun_prop
  exact dense_iInter_of_isOpen ho hd

theorem DevelopedFaces.interior_disks_disjoint (B : DevelopedFaces F out)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (z : ℂ → ℂ) (hz : ∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=B.radius (F i 0)+B.radius (F i 1))
    (C : ∀ d : {d : Faces F // d≠out},FacialCycle F d.val)
    (hpos : ∀ d,0<CannonTriangleWinding.area (z (C d).a) (z (C d).b) (z (C d).c))
    (hdis : Pairwise (fun d e=>Disjoint
      {p | CannonTriangleWinding.Inside (z (C d).a) (z (C d).b) (z (C d).c) p}
      {p | CannonTriangleWinding.Inside (z (C e).a) (z (C e).b) (z (C e).c) p}))
    {q v : ℂ} (hq : Vertex F q) (hv : Vertex F v)
    (hqo : q∉faceVertices F out) (hvo : v∉faceVertices F out) (hqv : q≠v) :
    Disjoint (ball (z q) (B.radius q)) (ball (z v) (B.radius v)) := by
  classical
  apply Set.disjoint_left.mpr
  intro p hp hp'
  have hd := developed_edges_generic_dense z B.radius B.radius_pos hlen
  obtain ⟨p,hp,hg⟩ := hd.inter_open_nonempty
    (ball (z q) (B.radius q)∩ball (z v) (B.radius v))
    (isOpen_ball.inter isOpen_ball) ⟨p,hp,hp'⟩
  have hgp : ∀ i,orientedArea (z (F i 0)) (z (F i 1)) p≠0 := mem_iInter.mp hg
  have hpq : dist (z q) p<B.radius q := by simpa only [mem_ball,dist_comm] using hp.1
  have hpv : dist (z v) p<B.radius v := by simpa only [mem_ball,dist_comm] using hp.2
  obtain ⟨d,hd,u,w,hqd,hud,hwd,hqu,hqw,huw,H⟩ := B.interior_ball_cover hF Q hQ hK z hz hq hqo hpq hgp
  obtain ⟨e,he,u',w',hve,hue,hwe,hvu,hvw,hu'w',H'⟩ := B.interior_ball_cover hF Q hQ hK z hz hv hvo hpv hgp
  have HP := (C ⟨d,hd⟩).inside_of_interior z (hpos _) hqd hud hwd hqu hqw huw H
  have HP' := (C ⟨e,he⟩).inside_of_interior z (hpos _) hve hue hwe hvu hvw hu'w' H'
  have hde : d=e := by
    by_contra hne
    exact Set.disjoint_left.mp (@hdis ⟨d,hd⟩ ⟨e,he⟩ (fun hh=>hne (congrArg Subtype.val hh))) HP HP'
  subst e
  have hlenqv : dist (z q) (z v)=B.radius q+B.radius v := by
    rw [hz d hd q hqd,hz d hd v hve]
    exact B.lengths d q hqd v hve hqv
  have ht := dist_triangle (z q) p (z v)
  rw [dist_comm p (z v),hlenqv] at ht
  linarith

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
