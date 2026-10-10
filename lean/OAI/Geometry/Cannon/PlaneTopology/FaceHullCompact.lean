import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.ClosedInsideSegment
import OAI.Geometry.Cannon.Conformal.SphereTile
import OAI.Geometry.Cannon.Modulus.BoundaryNormalizedAnnularCarriers

namespace OAI

section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding CannonTileTopology
open scoped OnePoint

attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)]

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma faceHull_compact (z : ℂ → ℂ) (d : Faces F) : IsCompact (faceHull F z d) :=
  ((faceVertices F d).finite_toSet.image z).isCompact_convexHull ℝ

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma FacialCycle.hull_regular {d : Faces F} (C : FacialCycle F d) (z : ℂ → ℂ)
    (hpos : 0<area (z C.a) (z C.b) (z C.c)) :
    closure (interior (faceHull F z d))=faceHull F z d := by
  rw [C.hull_eq,convexHull_interior hpos,convexHull_closure_inside hpos]

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma sphereTile_regular (z : ℂ → ℂ) (out d : Faces F)
    (hcycles : ∀ e : Faces F,∃ C : FacialCycle F e,0<area (z C.a) (z C.b) (z C.c)) :
    closure (interior (sphereTile F z out d))=sphereTile F z out d := by
  obtain ⟨C,hC⟩:=hcycles d
  have hc:=faceHull_compact z d
  have hr:=C.hull_regular z hC
  unfold sphereTile
  split_ifs with h
  · subst d
    rw [interior_compl,coe_closure_interior hc hr,closure_compl,coe_image_interior]
  · exact coe_regular hc hr

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma sphereTile_interiors_disjoint (z : ℂ → ℂ) (out : Faces F)
    (hcycles : ∀ e : Faces F,∃ C : FacialCycle F e,0<area (z C.a) (z C.b) (z C.c))
    (hI : ∀ d e : Faces F,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull F z d)) (interior (faceHull F z e)))
    (hfill : (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out) :
    Pairwise fun d e=>Disjoint (interior (sphereTile F z out d)) (interior (sphereTile F z out e)) := by
  have ho (d : Faces F) (hd : d≠out) :
      Disjoint (interior (sphereTile F z out d)) (interior (sphereTile F z out out)) := by
    obtain ⟨C,hC⟩:=hcycles out
    have hs : faceHull F z d⊆faceHull F z out := by
      rw [←hfill]
      exact subset_iUnion (fun e : {e : Faces F // e≠out}=>faceHull F z e.val) ⟨d,hd⟩
    simp only [sphereTile,ite_eq_right hd,ite_true,coe_image_interior,interior_compl,
      coe_closure_interior (faceHull_compact z out) (C.hull_regular z hC)]
    apply Set.disjoint_left.mpr
    rintro p ⟨q,hq,rfl⟩ hpo
    exact hpo ⟨q,hs (interior_subset hq),rfl⟩
  intro d e hde
  by_cases hd : d=out
  · subst d
    exact (ho e hde.symm).symm
  by_cases he : e=out
  · subst e
    exact ho d hd
  simp only [sphereTile,ite_eq_right hd,ite_eq_right he,coe_image_interior]
  exact (hI d e hd he hde).image OnePoint.coe_injective.injOn (subset_univ _) (subset_univ _)

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma sphereTile_frontier_disks (z : ℂ → ℂ) (r : ℂ → ℝ)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=r (F i 0)+r (F i 1))
    (hcycles : ∀ e : Faces F,∃ C : FacialCycle F e,0<area (z C.a) (z C.b) (z C.c)) (out d : Faces F) :
    frontier (sphereTile F z out d)⊆⋃ v∈(faceVertices F d : Set ℂ),
      ((↑) : ℂ → OnePoint ℂ) '' closedBall (z v) (r v) := by
  have he : frontier (sphereTile F z out d)=((↑) : ℂ → OnePoint ℂ) '' frontier (faceHull F z d) := by
    obtain ⟨C,hC⟩:=hcycles d
    unfold sphereTile
    split_ifs with h
    · subst d
      rw [frontier_compl,coe_interior_frontier (faceHull_compact z out) (C.hull_regular z hC)]
    · exact coe_frontier (faceHull_compact z d)
  rw [he]
  rintro p ⟨q,hq,rfl⟩
  obtain ⟨C,hC⟩:=hcycles d
  obtain ⟨u,hu,v,hv,huv,hq⟩:=C.frontier_edges z hC hq
  rcases segment_two_closedBalls (C.developed_length hu hv huv z r hlen) hq with h|h
  · exact mem_iUnion₂.mpr ⟨u,hu,⟨q,h,rfl⟩⟩
  · exact mem_iUnion₂.mpr ⟨v,hv,⟨q,h,rfl⟩⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding CannonTileTopology
open scoped OnePoint

attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)]

lemma face_incidence_card_le
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (N : ℕ)
    (hdeg : ∀ v : ℂ,Nat.card {i : ι | v∈range (F i)}≤N) (v : ℂ) :
    (Finset.univ.filter (fun d : Faces F=>v∈faceVertices F d)).card≤N := by
  classical
  by_cases hv : Vertex F v
  · obtain ⟨n,hn,e,a,-⟩:=vertexLink_order F hF Q hQ hK hv
    have he : Nat.card (IncidentFaces F v)=Nat.card (IncidentEdges F v):=
      Nat.card_congr (a.symm.trans e)
    let eqv : {d : Faces F // v∈faceVertices F d}≃IncidentFaces F v :=
      { toFun:=fun d=>⟨d.val,((mem_faceVertices F d.val v).mp d.property).2⟩
        invFun:=fun d=>⟨d.val,(mem_faceVertices F d.val v).mpr ⟨hv,d.property⟩⟩
        left_inv:=fun _=>rfl
        right_inv:=fun _=>rfl }
    have hc : Nat.card {d : Faces F // v∈faceVertices F d}≤N:=
      (Nat.card_congr eqv).trans he ▸ hdeg v
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using hc
  · have he : ∀ d : Faces F,v∉faceVertices F d:=fun d hh=>hv ((mem_faceVertices F d v).mp hh).1
    simp [he]

omit [DecidableEq ι] [Fintype (Faces F)] in
lemma packing_center_tile_incidence
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (z : ℂ → ℂ) (r : ℂ → ℝ) (hr : ∀ v,0<r v)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=r (F i 0)+r (F i 1))
    (hsep : ∀ u,Vertex F u → ∀ v,Vertex F v → u≠v → r u+r v≤dist (z u) (z v))
    (hcycles : ∀ d : Faces F,∃ C : FacialCycle F d,0<area (z C.a) (z C.b) (z C.c))
    (out : Faces F)
    (hI : ∀ d e : Faces F,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull F z d)) (interior (faceHull F z e)))
    (hfill : (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out)
    {v : ℂ} (hv : Vertex F v) (d : Faces F)
    (hvd : (z v:OnePoint ℂ)∈sphereTile F z out d) : v∈faceVertices F d := by
  by_contra hn
  obtain ⟨e,heo,hve⟩:=vertex_inner_face (out:=out) hF Q hQ hK hv
  have hpe : (z v:OnePoint ℂ)∈sphereTile F z out e := by
    rw [sphereTile,ite_eq_right heo]
    exact ⟨z v,subset_convexHull ℝ _ ⟨v,hve,rfl⟩,rfl⟩
  have hde : d≠e:=fun h=>hn (h ▸ hve)
  have hf:=(regular_tiles_inter_frontier (sphereTile_regular z out d hcycles)
    (sphereTile_regular z out e hcycles)
    (sphereTile_interiors_disjoint z out hcycles hI hfill hde) hvd hpe).1
  obtain ⟨j,hj,q,hq,he⟩:=mem_iUnion₂.mp (sphereTile_frontier_disks z r hlen hcycles out d hf)
  have hqv : q=z v:=OnePoint.coe_injective he
  subst q
  have hne : v≠j:=fun h=>hn (h ▸ hj)
  have hs:=hsep v hv j ((mem_faceVertices F d j).mp hj).1 hne
  have hd:=mem_closedBall.mp hq
  linarith [hr v]
end CannonEmbeddedArc.Arc

end
end

end OAI
