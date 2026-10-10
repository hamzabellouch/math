import Mathlib
import OAI.Geometry.HyperbolicGroups.SmallSimplexCoordinates
import OAI.Geometry.HyperbolicGroups.TriangleEdgeIntersection
import OAI.Geometry.HyperbolicGroups.VoltagePrismGluing

namespace OAI

/-! Constructions of the actual face-prism input: every edge, and every
nondegenerate triangle with a literal three-sided contracting prism. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open TriangleSquare
variable {V : Type*} [Fintype V] [DecidableEq V] {K : AbstractSimplicialComplex V}
  {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  (v : Voltage K G) (z : v.TotalSpace) (E : v.EdgePrisms z)

variable {a b : V} (h : {a,b} ∈ K.faces)
def edgeFacePrism : v.FacePrism z E {a,b} h where
  anchor := a
  mem_anchor := by simp
  H g := (E.H h g).comp ⟨fun tx => (tx.1,edgeParameter tx.2),
    continuous_fst.prodMk ((edgeParameter_continuous a b).comp continuous_snd)⟩
  initial g x := by
    change E.H h g (0,edgeParameter x) = _
    rw [E.initial]
    change v.faceLift h (a := a) (by simp) g (edgePoint h (edgeParameter x)) = _
    rw [edgePoint_parameter]
  final g x := E.final h g (edgeParameter x)
  edge h' g k t r x he := by
    apply E.agree
    change v.faceLift h (a := a) (by simp) g (edgePoint h (edgeParameter x)) = _
    rw [edgePoint_parameter]
    exact he

variable {c : V} (ht : {a,b,c} ∈ K.faces) (hi : Function.Injective ![a,b,c])
variable (H : G → C(I × Triangle,v.TotalSpace))
  (h0 : ∀ g p, H g (0,p) = v.triangleLift ht g p)
  (h1 : ∀ g p, H g (1,p) = z)
  (hb : ∀ g t r, H g (t,quotient (r,0)) = E.H (edge_of_subset K ht (by simp) (by simp) : {a,b} ∈ K.faces) g (t,r))
  (hl : ∀ g t r, H g (t,quotient (0,r)) = E.H (edge_of_subset K ht (by simp) (by simp) : {a,c} ∈ K.faces) g (t,r))
  (hr : ∀ g t r, H g (t,quotient (1,r)) = E.H (edge_of_subset K ht (by simp) (by simp) : {b,c} ∈ K.faces) (g*v.value a b) (t,r))

lemma triangleCoordinates_symm_point (x : closedFace (K := K) {a,b,c}) :
    trianglePoint ht ((triangleCoordinates ht hi).symm x) = x := by
  rw [←triangleCoordinates_apply ht hi,(triangleCoordinates ht hi).apply_symm_apply]

include hi hb hl hr in
lemma trianglePrism_edge_agree {d e : V} (h' : {d,e} ∈ K.faces) (g k : G) (t r : I)
    (p : Triangle) (he : v.triangleLift ht g p = v.edgeLift h' k r) :
    H g (t,p) = E.H h' k (t,r) := by
  have hp : (trianglePoint ht p).val = edgePath K h' r := congrArg v.proj he
  rcases triangle_boundary_of_edge ht hi h' p r hp with ⟨s,rfl⟩|⟨s,rfl⟩|⟨s,rfl⟩
  · rw [hb]
    apply E.agree
    exact (v.triangleLift_bottom ht g s).symm.trans he
  · rw [hl]
    apply E.agree
    exact (v.triangleLift_left ht g s).symm.trans he
  · rw [hr]
    apply E.agree
    exact (v.triangleLift_right ht g s).symm.trans he

def triangleFacePrism : v.FacePrism z E {a,b,c} ht where
  anchor := a
  mem_anchor := by simp
  H g := (H g).comp ((ContinuousMap.id I).prodMap
    ⟨(triangleCoordinates ht hi).symm,(triangleCoordinates ht hi).symm.continuous⟩)
  initial g x := by
    change H g (0,(triangleCoordinates ht hi).symm x) = _
    rw [h0]
    change v.faceLift ht (a := a) (by simp) g (trianglePoint ht ((triangleCoordinates ht hi).symm x)) = _
    rw [triangleCoordinates_symm_point ht hi]
  final g x := h1 g ((triangleCoordinates ht hi).symm x)
  edge h' g k t r x he := by
    apply v.trianglePrism_edge_agree z E ht hi H hb hl hr
    change v.faceLift ht (a := a) (by simp) g (trianglePoint ht ((triangleCoordinates ht hi).symm x)) = _
    rw [triangleCoordinates_symm_point ht hi]
    exact he

variable (hd : ∀ s ∈ K.faces, s.card ≤ 3)
  (hf : ∀ s (hs : s ∈ K.faces), s.card = 3 → Nonempty (v.FacePrism z E s hs))
include hd hf in
lemma facePrism_exists (s : Finset V) (hs : s ∈ K.faces) : Nonempty (v.FacePrism z E s hs) := by
  by_cases hc : s.card ≤ 2
  · obtain ⟨a,b,rfl⟩ := nonempty_pair_of_card_le_two (K.isRelLowerSet_faces hs).1 hc
    exact ⟨v.edgeFacePrism z E hs⟩
  · exact hf s hs (by have := hd s hs; omega)

def fromTrianglePrisms : C(I × v.TotalSpace,v.TotalSpace) :=
  v.contraction z E (fun s hs => Classical.choice (v.facePrism_exists z E hd hf s hs)) hd

lemma fromTrianglePrisms_initial (e : v.TotalSpace) : v.fromTrianglePrisms z E hd hf (0,e) = e :=
  v.contraction_initial z E _ hd e
lemma fromTrianglePrisms_final (e : v.TotalSpace) : v.fromTrianglePrisms z E hd hf (1,e) = z :=
  v.contraction_final z E _ hd e

lemma fromTrianglePrisms_edge {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t r : I) :
    v.fromTrianglePrisms z E hd hf (t,v.edgeLift h g r) = E.H h g (t,r) :=
  v.contraction_edge z E _ hd h g t r

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
