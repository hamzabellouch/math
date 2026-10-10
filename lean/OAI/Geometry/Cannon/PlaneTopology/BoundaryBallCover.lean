import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.InteriorBallCover
import OAI.Geometry.Cannon.CirclePacking.OpenEuclideanFan
import OAI.Geometry.Cannon.PlanarGraphs.CutOrder

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

theorem DevelopedFaces.boundary_ball_cover (B : DevelopedFaces F out)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (z : ℂ → ℂ) (hz : ∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=B.radius (F i 0)+B.radius (F i 1))
    {q : ℂ} (hq : Vertex F q) (hqo : q∈faceVertices F out)
    {p : ℂ} (hp : dist (z q) p<B.radius q)
    (houter : ∀ u∈faceVertices F out,∀ v∈faceVertices F out,
      q≠u → q≠v → u≠v → TriInterior (z q) (z u) (z v) p)
    (hgen : ∀ i,orientedArea (z (F i 0)) (z (F i 1)) p≠0) :
    ∃ d : Faces F,d≠out ∧ ∃ u v : ℂ,
      q∈faceVertices F d ∧ u∈faceVertices F d ∧ v∈faceVertices F d ∧
      q≠u ∧ q≠v ∧ u≠v ∧ TriInterior (z q) (z u) (z v) p := by
  classical
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  have hmem (d : IncidentFaces F q) : q∈faceVertices F d.val := (mem_faceVertices F _ _).mpr ⟨hq,d.property⟩
  have hsum : (∑ d : IncidentFaces F q,B.angle d.val q)=Real.pi/3 := by
    have hh := Fintype.sum_subtype_add_sum_subtype (fun d : Faces F=>q∈closure (face F d)) (fun d=>B.angle d q)
    have hzz : (∑ d : {d : Faces F // ¬q∈closure (face F d)},B.angle d.val q)=0 := by
      apply Finset.sum_eq_zero
      intro faceIndex _
      exact B.angle_zero _ _ (fun membership=>faceIndex.property ((mem_faceVertices F _ _).mp membership).2)
    rw [hzz,add_zero,B.angle_sum q hq,ite_eq_left hqo] at hh
    exact hh
  obtain ⟨n,hn,e,a,hn2,hei,hen⟩ := vertexLink_order F hF Q hQ hK hq
  let o : Fin n := a.symm ⟨out,((mem_faceVertices F _ _).mp hqo).2⟩
  have ho : (a o).val=out := by simp [o]
  have hinner (i : Fin n) (hi : i≠o) : (a i).val≠out := by
    intro H
    exact hi (a.injective (Subtype.ext (H.trans ho.symm)))
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
  have hop (i : Fin n) (hi : i≠o) (hni : nx i≠o) : orientedArea (z q) (z (w (nx i))) (z (w i))*
      orientedArea (z q) (z (w (nx i))) (z (w (nx (nx i))))<0 := by
    let j := (e (nx i)).val
    have had : (a i).val≠(a (nx i)).val := fun hh=>hnxi i (a.injective (Subtype.ext hh)).symm
    have hq0 : q∈faceVertices F (a (nx i)).val := (hm (nx i)).1
    have hw0 : w (nx i)∈faceVertices F (a (nx i)).val := (hm (nx i)).2.1
    have hsp : Spans (F j) q (w (nx i)) := hw (nx i)
    rcases hsp with ⟨he0,he1⟩|⟨he0,he1⟩
    · have H := B.opposite j (a i).val (a (nx i)).val had (hinner i hi) (hinner (nx i) hni) (hen i) (hei (nx i))
        (w i) (hm i).2.1 (by rw [he0]; exact (hw i).ne.symm) (by rw [he1]; exact hww i)
        (w (nx (nx i))) (hm (nx i)).2.2 (by rw [he0]; exact (hw (nx (nx i))).ne.symm)
        (by rw [he1]; exact (hww (nx i)).symm)
      rw [he0,he1,←hz _ (hinner (nx i) hni) _ hq0,←hz _ (hinner (nx i) hni) _ hw0,
        ←hz _ (hinner i hi) _ (hm i).2.1,←hz _ (hinner (nx i) hni) _ (hm (nx i)).2.2] at H
      exact H
    · have H := B.opposite j (a i).val (a (nx i)).val had (hinner i hi) (hinner (nx i) hni) (hen i) (hei (nx i))
        (w i) (hm i).2.1 (by rw [he1]; exact hww i) (by rw [he0]; exact (hw i).ne.symm)
        (w (nx (nx i))) (hm (nx i)).2.2 (by rw [he1]; exact (hww (nx i)).symm)
        (by rw [he0]; exact (hw (nx (nx i))).ne.symm)
      rw [he0,he1,←hz _ (hinner (nx i) hni) _ hq0,←hz _ (hinner (nx i) hni) _ hw0,
        ←hz _ (hinner i hi) _ (hm i).2.1,←hz _ (hinner (nx i) hni) _ (hm (nx i)).2.2] at H
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

  let rot := CannonCycleOrder.cutOrder hn o
  have hrnext (k : ℕ) : rot (k+1)=nx (rot k) := CannonCycleOrder.cutOrder_next hn o k
  have hrne (k : ℕ) (hk : k<n-1) : rot k≠o := CannonCycleOrder.cutOrder_ne hn o hk
  have hr0 : rot 0=nx o := CannonCycleOrder.cutOrder_first hn o
  have hrn : rot (n-1)=o := CannonCycleOrder.cutOrder_last hn o
  have hab (i : Fin n) : dist (z q) (z (w i))=B.radius q+B.radius (w i) := by
    have H:=hlen (e i).val
    rcases hw i with ⟨h0,h1⟩|⟨h0,h1⟩
    · simpa only [h0,h1] using H
    · simpa only [h0,h1,dist_comm,add_comm] using H
  have hbc (i : Fin n) (hi : i≠o) :
      dist (z (w i)) (z (w (nx i)))=B.radius (w i)+B.radius (w (nx i)) := by
    rw [hz _ (hinner i hi) _ (hm i).2.1,hz _ (hinner i hi) _ (hm i).2.2]
    exact B.lengths _ _ (hm i).2.1 _ (hm i).2.2 (hww i)
  have ht : ∑ k∈Finset.range (n-1),B.angle (a (rot k)).val q=Real.pi/3 := by
    rw [CannonCycleOrder.sum_cutOrder hn o (fun i=>B.angle (a i).val q) (by rw [ho]; exact B.angle_out q)]
    exact (a.sum_comp (fun d=>B.angle d.val q)).trans hsum
  have hOut : TriInterior (z q) (z (w (rot 0))) (z (w (rot (n-1)))) p := by
    rw [hr0,hrn]
    apply houter _ (by rw [←ho]; exact (hm o).2.2) _ (by rw [←ho]; exact (hm o).2.1)
      (hw (nx o)).ne (hw o).ne (hww o).symm
  obtain ⟨k,hk,H⟩:=open_star_ball_cover (n-1) (by omega) (B.radius q)
    (fun k=>B.radius (w (rot k))) (fun k=>B.angle (a (rot k)).val q)
    (B.radius_pos q) (fun index _=>B.radius_pos (w (rot index))) (fun k hk=>B.angle_pos _ (hinner _ (hrne k hk)) q (hm _).1)
    (by rw [ht]; exact ⟨by positivity,by linarith [Real.pi_pos]⟩)
    (fun k hk=>by
      rw [hrnext]
      exact B.cosine _ (hinner _ (hrne k hk)) q (hm _).1 _ (hm _).2.1 _ (hm _).2.2
        (hw _).ne (hw _).ne (hww _))
    (z q) (fun k=>z (w (rot k))) (fun index _=>hab (rot index))
    (fun k hk=>by rw [hrnext]; exact hbc _ (hrne k hk))
    (fun k hk=>by
      have hstep : rot (k+2)=nx (nx (rot k)) := by rw [show k+2=(k+1)+1 by omega,hrnext,hrnext]
      rw [hstep,hrnext]
      exact hop _ (hrne k (by omega)) (by rw [←hrnext]; exact hrne (k+1) hk)) hp hOut (fun index _=>hgp (rot index))
  rw [hrnext] at H
  exact ⟨(a (rot k)).val,hinner _ (hrne k hk),w (rot k),w (nx (rot k)),
    (hm _).1,(hm _).2.1,(hm _).2.2,(hw _).ne,(hw _).ne,hww _,H⟩

end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι]
variable {F : ι → Arc ℂ} {d : Faces F}

lemma FacialCycle.pair_edge (C : FacialCycle F d) {u v : ℂ}
    (hu : u∈faceVertices F d) (hv : v∈faceVertices F d) (huv : u≠v) :
    ∃ i,Spans (F i) u v := by
  rw [C.vertices] at hu hv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
  rcases hu with rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl
  all_goals first
    | exact (huv rfl).elim
    | exact ⟨C.e,C.spans_e⟩
    | exact ⟨C.e,C.spans_e.symm⟩
    | exact ⟨C.f,C.spans_f⟩
    | exact ⟨C.f,C.spans_f.symm⟩
    | exact ⟨C.g,C.spans_g⟩
    | exact ⟨C.g,C.spans_g.symm⟩

omit [Fintype ι] in
lemma Spans.developed_length {i : ι} {u v : ℂ} (h : Spans (F i) u v)
    (z : ℂ → ℂ) (r : ℂ → ℝ)
    (hlen : dist (z (F i 0)) (z (F i 1))=r (F i 0)+r (F i 1)) :
    dist (z u) (z v)=r u+r v := by
  rcases h with ⟨h0,h1⟩|⟨h0,h1⟩
  · simpa only [h0,h1] using hlen
  · simpa only [h0,h1,dist_comm,add_comm] using hlen

lemma FacialCycle.developed_length (C : FacialCycle F d) {u v : ℂ}
    (hu : u∈faceVertices F d) (hv : v∈faceVertices F d) (huv : u≠v)
    (z : ℂ → ℂ) (r : ℂ → ℝ)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=r (F i 0)+r (F i 1)) :
    dist (z u) (z v)=r u+r v := by
  obtain ⟨i,hi⟩:=C.pair_edge hu hv huv
  exact hi.developed_length z r (hlen i)

lemma FacialCycle.interior_of_inside (C : FacialCycle F d) (z : ℂ → ℂ)
    (r : ℂ → ℝ) (hr : ∀ q,0<r q)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=r (F i 0)+r (F i 1))
    (hpos : 0<CannonTriangleWinding.area (z C.a) (z C.b) (z C.c))
    {q u v p : ℂ} (hq : q∈faceVertices F d) (hu : u∈faceVertices F d) (hv : v∈faceVertices F d)
    (hqu : q≠u) (hqv : q≠v) (huv : u≠v)
    (h : CannonTriangleWinding.Inside (z C.a) (z C.b) (z C.c) p) :
    TriInterior (z q) (z u) (z v) p := by
  classical
  have htri : TriInterior (z C.a) (z C.b) (z C.c) p := by
    apply TriInterior.of_positive
    · rwa [←winding_area_eq]
    · rw [←winding_area_eq]; exact h.1
    · rw [←winding_area_eq]; exact h.2.1
    · rw [←winding_area_eq]; exact h.2.2
  have mem {x : ℂ} (hx : x∈faceVertices F d) : z x∈({z C.a,z C.b,z C.c}:Finset ℂ) := by
    rw [C.vertices] at hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢
    rcases hx with rfl|rfl|rfl <;> simp
  have ne {x y : ℂ} (hx : x∈faceVertices F d) (hy : y∈faceVertices F d) (hxy : x≠y) : z x≠z y := by
    intro H
    have HH:=C.developed_length hx hy hxy z r hlen
    rw [H,dist_self] at HH
    linarith [hr x,hr y]
  exact htri.of_vertices (mem hq) (mem hu) (mem hv) (ne hq hu hqu) (ne hq hv hqv) (ne hu hv huv)

end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry CannonTriangleBoundary

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}
attribute [local instance] Classical.propDecidable

theorem DevelopedFaces.disk_disjoint_of_interior (B : DevelopedFaces F out)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (z : ℂ → ℂ) (hz : ∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=B.radius (F i 0)+B.radius (F i 1))
    (C : ∀ d : {d : Faces F // d≠out},FacialCycle F d.val) (O : FacialCycle F out)
    (hpos : ∀ d,0<CannonTriangleWinding.area (z (C d).a) (z (C d).b) (z (C d).c))
    (ho : 0<CannonTriangleWinding.area (z O.a) (z O.b) (z O.c))
    (hchain : ∀ f : ℂ → ℂ → ℤ,(∀ x y,f y x= -f x y) →
      (∑ d,cycle (fun x y=>f (z x) (z y)) (C d).a (C d).b (C d).c)=
        cycle f (z O.a) (z O.b) (z O.c))
    (hdis : Pairwise (fun d e=>Disjoint
      {p | CannonTriangleWinding.Inside (z (C d).a) (z (C d).b) (z (C d).c) p}
      {p | CannonTriangleWinding.Inside (z (C e).a) (z (C e).b) (z (C e).c) p}))
    {q v : ℂ} (hq : Vertex F q) (hv : Vertex F v)
    (hqo : q∉faceVertices F out) (hqv : q≠v) :
    Disjoint (ball (z q) (B.radius q)) (ball (z v) (B.radius v)) := by
  classical
  by_cases hvo : v∈faceVertices F out
  swap
  · exact B.interior_disks_disjoint hF Q hQ hK z hz hlen C hpos hdis hq hv hqo hvo hqv
  apply Set.disjoint_left.mpr
  intro p hp hp'
  have hd := developed_edges_generic_dense z B.radius B.radius_pos hlen
  have hg (d : {d : Faces F // d≠out}) := CannonTriangleWinding.generic_dense_open
    (z (C d).a) (z (C d).b) (z (C d).c)
    (CannonTriangleWinding.area_pos_distinct (hpos d)).1
    (CannonTriangleWinding.area_pos_distinct (hpos d)).2.1
    (CannonTriangleWinding.area_pos_distinct (hpos d)).2.2
  have hgo := CannonTriangleWinding.generic_dense_open (z O.a) (z O.b) (z O.c)
    (CannonTriangleWinding.area_pos_distinct ho).1
    (CannonTriangleWinding.area_pos_distinct ho).2.1
    (CannonTriangleWinding.area_pos_distinct ho).2.2
  have hD := dense_iInter_of_isOpen (fun d=>(hg d).2) (fun d=>(hg d).1)
  have hAll:= (hd.inter_of_isOpen_right hD (isOpen_iInter_of_finite fun d=>(hg d).2)).inter_of_isOpen_right hgo.1 hgo.2
  obtain ⟨p,hp,hg⟩:=hAll.inter_open_nonempty
    (ball (z q) (B.radius q)∩ball (z v) (B.radius v))
    (isOpen_ball.inter isOpen_ball) ⟨p,hp,hp'⟩
  have hgp : ∀ i,orientedArea (z (F i 0)) (z (F i 1)) p≠0 := mem_iInter.mp hg.1.1
  have hpq : dist (z q) p<B.radius q := by simpa only [mem_ball,dist_comm] using hp.1
  have hpv : dist (z v) p<B.radius v := by simpa only [mem_ball,dist_comm] using hp.2
  obtain ⟨d,hd,u,w,hqd,hud,hwd,hqu,hqw,huw,H⟩:=B.interior_ball_cover hF Q hQ hK z hz hq hqo hpq hgp
  have HP:=(C ⟨d,hd⟩).inside_of_interior z (hpos _) hqd hud hwd hqu hqw huw H
  have HO : CannonTriangleWinding.Inside (z O.a) (z O.b) (z O.c) p := by
    apply (CannonTriangleWinding.generic_union_iff
      (fun d=>z (C d).a) (fun d=>z (C d).b) (fun d=>z (C d).c)
      (z O.a) (z O.b) (z O.c) p hpos ho (mem_iInter.mp hg.1.2) hg.2 hchain).mp
    exact ⟨⟨d,hd⟩,HP⟩
  obtain ⟨e,he,u',w',hve,hue,hwe,hvu,hvw,hu'w',H'⟩:=B.boundary_ball_cover hF Q hQ hK z hz hlen hv hvo hpv
    (fun u hu w hw hvu hvw huw=>O.interior_of_inside z B.radius B.radius_pos hlen ho hvo hu hw hvu hvw huw HO) hgp
  have HP':=(C ⟨e,he⟩).inside_of_interior z (hpos _) hve hue hwe hvu hvw hu'w' H'
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

theorem DevelopedFaces.circle_packing (B : DevelopedFaces F out)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (hthree : ∀ d,(faceVertices F d).card=3) :
    ∃ z : ℂ → ℂ,
      (∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q) ∧
      (∀ i,dist (z (F i 0)) (z (F i 1))=B.radius (F i 0)+B.radius (F i 1)) ∧
      ∀ q,Vertex F q → ∀ v,Vertex F v → q≠v →
        B.radius q+B.radius v≤dist (z q) (z v) := by
  obtain ⟨z,C,O,hz,hlen,hpos,ho,hchain,hdis⟩:=B.univalent_triangles hF Q hQ hK hthree
  refine ⟨z,hz,hlen,?_⟩
  intro q hq v hv hqv
  by_cases hqo : q∈faceVertices F out
  · by_cases hvo : v∈faceVertices F out
    · exact (O.developed_length hqo hvo hqv z B.radius hlen).ge
    · have H:=B.disk_disjoint_of_interior hF Q hQ hK z hz hlen C O hpos ho
        (hchain ℤ) hdis hv hq hvo hqv.symm
      have HH:=(disjoint_ball_ball_iff (B.radius_pos v) (B.radius_pos q)).mp H
      simpa only [add_comm,dist_comm] using HH
  · have H:=B.disk_disjoint_of_interior hF Q hQ hK z hz hlen C O hpos ho
      (hchain ℤ) hdis hq hv hqo hqv
    exact (disjoint_ball_ball_iff (B.radius_pos q) (B.radius_pos v)).mp H

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
