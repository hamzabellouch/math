import Mathlib
import OAI.Geometry.Cannon.CirclePacking.OpenEuclideanFan
import OAI.Geometry.Cannon.PlanarGraphs.CutOrder
import OAI.Geometry.Cannon.CirclePacking.PetalAngle
import OAI.Geometry.Cannon.PlaneTopology.BoundaryBallCover

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

theorem DevelopedFaces.interior_radius_control (B : DevelopedFaces F out)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (z : ℂ → ℂ) (hz : ∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q)
    (hpack : ∀ u,Vertex F u → ∀ v,Vertex F v → u≠v →
      B.radius u+B.radius v≤dist (z u) (z v))
    (N : ℕ) (c : ℝ) (hc : 0<c)
    (hring : ∀ n≤N,∀ t α : ℕ → ℝ,RingData n t α → ∀ i<n,c≤t i)
    {q v : ℂ} {j : ι} (hq : Vertex F q) (hqo : q∉faceVertices F out)
    (hdegree : Nat.card (IncidentEdges F q)≤N) (hv : Spans (F j) q v) :
    c*B.radius q≤B.radius v := by
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
  obtain ⟨t,β,hdata,hfrac⟩ := actual_fan_ringData hn (B.radius q) (fun i=>B.radius (w i))
    (fun i=>B.angle (a i).val q) (B.radius_pos q) (fun i=>B.radius_pos _)
    (fun i=>B.angle_pos _ (hinner _) q (hm i).1)
    ((a.sum_comp (fun d=>B.angle d.val q)).trans hsum)
    (fun i=>B.cosine _ (hinner _) q (hm i).1 _ (hm i).2.1 _ (hm i).2.2
      (hw i).ne (hw (nx i)).ne (hww i)) (z q) (fun i=>z (w i))
    (fun i=>len (a i) (hm i).1 (hm i).2.1 (hw i).ne)
    (fun i=>len (a i) (hm i).2.1 (hm i).2.2 (hww i)) hop
    (fun i j hij=>hpack _ (hw i).vertex_right _ (hw j).vertex_right (fun hh=>hij (hwinj hh)))
  have hnN : n≤N := by
    have he := Nat.card_congr e
    rw [Nat.card_fin] at he
    omega
  let k : Fin n := e.symm ⟨j,hv.mem_left⟩
  have heq : (e k).val=j := congrArg Subtype.val (e.apply_symm_apply ⟨j,hv.mem_left⟩)
  have hwv : w k=v := (heq ▸ hw k).other_unique hv
  have H := hring n hnN t β hdata k.val k.isLt
  rw [hfrac k,hwv] at H
  have H' := (le_div_iff₀ (add_pos (B.radius_pos q) (B.radius_pos v))).mp H
  nlinarith [mul_pos hc (B.radius_pos v)]

theorem exists_interior_radius_constant (N : ℕ) : ∃ c : ℝ,0<c ∧ c≤1 ∧
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
      (F : ι → Arc ℂ) [Fintype (Faces F)] (out : Faces F) (B : DevelopedFaces F out),
      Pairwise (fun i j=>Compatible (F i) (F j)) →
      ∀ Q : Finset (ℂ × ℂ),(∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2) →
      (∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) →
      ∀ z : ℂ → ℂ,(∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q) →
      (∀ u,Vertex F u → ∀ v,Vertex F v → u≠v →B.radius u+B.radius v≤dist (z u) (z v)) →
      ∀ q v j,Vertex F q → q∉faceVertices F out → Nat.card (IncidentEdges F q)≤N →
        Spans (F j) q v → c*B.radius q≤B.radius v := by
  obtain ⟨c,hc,hc1,hring⟩ := exists_bounded_ring_constant N
  refine ⟨c,hc,hc1,?_⟩
  intro ι _ _ _ F _ out B hF Q hQ hK z hz hpack q v j hq hqo hdeg hv
  exact B.interior_radius_control hF Q hQ hK z hz hpack N c hc hring hq hqo hdeg hv

end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}
attribute [local instance] Classical.propDecidable

theorem DevelopedFaces.boundary_corner_equation (B : DevelopedFaces F out)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (z : ℂ → ℂ) (hz : ∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=B.radius (F i 0)+B.radius (F i 1))
    (O : FacialCycle F out) {q : ℂ} (hq : Vertex F q) (hqo : q∈faceVertices F out) :
    ∃ u v : ℂ,u∈faceVertices F out ∧ v∈faceVertices F out ∧ q≠u ∧ q≠v ∧ u≠v ∧
      (B.radius q)^2+B.radius q*(B.radius u+B.radius v)=3*B.radius u*B.radius v := by
  classical
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  have hmem (d : IncidentFaces F q) : q∈faceVertices F d.val := (mem_faceVertices F _ _).mpr ⟨hq,d.property⟩
  have hsum : (∑ d : IncidentFaces F q,B.angle d.val q)=Real.pi/3 := by
    have hh := Fintype.sum_subtype_add_sum_subtype (fun d : Faces F=>q∈closure (face F d)) (fun d=>B.angle d q)
    have hzz : (∑ d : {d : Faces F // ¬q∈closure (face F d)},B.angle d.val q)=0 := by
      apply Finset.sum_eq_zero
      intro d hd
      exact B.angle_zero _ _ (fun h=>d.property ((mem_faceVertices F _ _).mp h).2)
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
  let L : ℕ → ℝ := fun k=>B.radius q+B.radius (w (rot k))
  let α : ℕ → ℝ := fun k=>B.angle (a (rot k)).val q
  let dd : ℕ → ℝ := fun k=>B.radius (w (rot k))+B.radius (w (rot (k+1)))
  obtain ⟨E,hEq,hEw⟩:=open_fan_global_frame (n-1) (by omega) L α dd
    (fun k hk=>add_pos (B.radius_pos _) (B.radius_pos _))
    (fun k hk=>add_pos (B.radius_pos _) (B.radius_pos _))
    (fun k hk=>B.angle_pos _ (hinner _ (hrne k hk)) q (hm _).1)
    (fun k hk=>by
      dsimp [L,α,dd]
      rw [hrnext]
      exact B.cosine _ (hinner _ (hrne k hk)) q (hm _).1 _ (hm _).2.1 _ (hm _).2.2
        (hw _).ne (hw _).ne (hww _))
    (z q) (fun k=>z (w (rot k))) (fun k hk=>hab _)
    (fun k hk=>by dsimp [dd]; rw [hrnext]; exact hbc _ (hrne k hk))
    (fun k hk=>by
      have hstep : rot (k+2)=nx (nx (rot k)) := by rw [show k+2=(k+1)+1 by omega,hrnext,hrnext]
      rw [hstep,hrnext]
      exact hop _ (hrne k (by omega)) (by rw [←hrnext]; exact hrne (k+1) hk))
  have hu : w (rot 0)∈faceVertices F out := by rw [hr0,←ho]; exact (hm o).2.2
  have hv : w (rot (n-1))∈faceVertices F out := by rw [hrn,←ho]; exact (hm o).2.1
  have huv : w (rot 0)≠w (rot (n-1)) := by rw [hr0,hrn]; exact (hww o).symm
  refine ⟨w (rot 0),w (rot (n-1)),hu,hv,(hw _).ne,(hw _).ne,huv,?_⟩
  have hd := O.developed_length hu hv huv z B.radius hlen
  have H:=fanRay_dist_sq_pair L α 0 (n-1)
  rw [←hEw 0 (by omega),←hEw (n-1) le_rfl,E.dist_eq,hd] at H
  have htotal : ∑ k∈Finset.range (n-1),α k=Real.pi/3 := ht
  simp only [Finset.range_zero,Finset.sum_empty,htotal,zero_sub,Real.cos_neg,Real.cos_pi_div_three] at H
  dsimp [L] at H
  nlinarith only [H]

theorem DevelopedFaces.outer_radius_eq (B : DevelopedFaces F out)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (z : ℂ → ℂ) (hz : ∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=B.radius (F i 0)+B.radius (F i 1))
    (O : FacialCycle F out) :
    ∀ u∈faceVertices F out,∀ v∈faceVertices F out,B.radius u=B.radius v := by
  classical
  have hn : (faceVertices F out).Nonempty := by rw [O.vertices]; simp
  obtain ⟨q,hq,hmax⟩ := (faceVertices F out).exists_max_image B.radius hn
  obtain ⟨u,v,hu,hv,hqu,hqv,huv,H⟩ := B.boundary_corner_equation hF Q hQ hK z hz hlen O
    ((mem_faceVertices F _ _).mp hq).1 hq
  have hsu : B.radius u≤B.radius q := hmax u hu
  have hsv : B.radius v≤B.radius q := hmax v hv
  have hsquare : B.radius u*B.radius v≤(B.radius q)^2 := by
    simpa only [pow_two] using mul_le_mul hsu hsv (B.radius_pos v).le (B.radius_pos q).le
  have hru : B.radius q=B.radius u := by
    have hmul := mul_le_mul_of_nonneg_left hsv (B.radius_pos u).le
    have htemp : B.radius q*B.radius v≤B.radius u*B.radius v := by nlinarith only [H,hsquare,hmul]
    exact le_antisymm ((mul_le_mul_iff_of_pos_right (B.radius_pos v)).mp htemp) hsu
  have hrv : B.radius q=B.radius v := by
    rw [←hru] at H
    have htemp : B.radius q*(B.radius q-B.radius v)=0 := by nlinarith only [H]
    exact sub_eq_zero.mp ((mul_eq_zero.mp htemp).resolve_left (B.radius_pos q).ne')
  have hcard : (faceVertices F out).card=3 := by
    rw [O.vertices]
    simp [O.ab,O.bc,O.ac]
  have hsub : ({q,u,v}:Finset ℂ)⊆faceVertices F out := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl <;> assumption
  have heq : ({q,u,v}:Finset ℂ)=faceVertices F out := Finset.eq_of_subset_of_card_le hsub (by
    rw [hcard]
    simp [hqu,hqv,huv])
  have hall : ∀ x∈faceVertices F out,B.radius x=B.radius q := by
    intro x hx
    rw [←heq] at hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl
    · rfl
    · exact hru.symm
    · exact hrv.symm
  exact fun u hu v hv=>(hall u hu).trans (hall v hv).symm

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
