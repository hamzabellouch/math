import Mathlib
import OAI.Geometry.HyperbolicGroups.SimplexCoordinates
import OAI.Geometry.HyperbolicGroups.TriangleSquare
import OAI.Geometry.HyperbolicGroups.VoltageEdges

namespace OAI

/-! Exact triangular coordinates in the independent lifted cells. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open TriangleSquare
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

omit [Fintype V] in
lemma triangle_image (a b c : V) : Finset.univ.image ![a,b,c] = {a,b,c} := by
  ext j
  simp [Fin.exists_fin_succ,eq_comm]

variable {v}
def trianglePoint {a b c : V} (h : {a,b,c} ∈ K.faces) : C(Triangle,closedFace (K := K) {a,b,c}) := by
  let f : C(Triangle,simplex {a,b,c}) :=
    ⟨fun z => ⟨barycentric ![a,b,c] z, by
      have hz := barycentric_mem ![a,b,c] z
      rw [triangle_image] at hz
      exact hz⟩, by
      apply Continuous.subtype_mk
      exact (barycentric_continuous ![a,b,c]).comp continuous_subtype_val⟩
  exact (⟨closedSimplexHomeomorph K h,(closedSimplexHomeomorph K h).continuous⟩ : C(simplex {a,b,c},closedFace (K := K) {a,b,c})).comp f

lemma trianglePoint_bottom {a b c : V} (h : {a,b,c} ∈ K.faces) (s : I) :
    (trianglePoint h (quotient (s,0))).val =
      edgePath K (edge_of_subset K h (by simp) (by simp) : {a,b} ∈ K.faces) s := by
  apply Subtype.ext
  funext j
  change barycentric ![a,b,c] (quotient (s,0)).val j =
    (AffineMap.lineMap (vertex K a).val (vertex K b).val (s:ℝ)) j
  rw [quotient_zero]
  simp [barycentric,Fin.sum_univ_succ,AffineMap.lineMap_apply_module,vertex,Pi.single_apply,eq_comm]

lemma trianglePoint_left {a b c : V} (h : {a,b,c} ∈ K.faces) (s : I) :
    (trianglePoint h (quotient (0,s))).val =
      edgePath K (edge_of_subset K h (by simp) (by simp) : {a,c} ∈ K.faces) s := by
  apply Subtype.ext
  funext j
  change barycentric ![a,b,c] (quotient (0,s)).val j =
    (AffineMap.lineMap (vertex K a).val (vertex K c).val (s:ℝ)) j
  rw [quotient_left]
  simp [barycentric,Fin.sum_univ_succ,AffineMap.lineMap_apply_module,vertex,Pi.single_apply,eq_comm]

lemma trianglePoint_right {a b c : V} (h : {a,b,c} ∈ K.faces) (s : I) :
    (trianglePoint h (quotient (1,s))).val =
      edgePath K (edge_of_subset K h (by simp) (by simp) : {b,c} ∈ K.faces) s := by
  apply Subtype.ext
  funext j
  change barycentric ![a,b,c] (quotient (1,s)).val j =
    (AffineMap.lineMap (vertex K b).val (vertex K c).val (s:ℝ)) j
  rw [quotient_right]
  simp [barycentric,Fin.sum_univ_succ,AffineMap.lineMap_apply_module,vertex,Pi.single_apply,eq_comm]

variable (v)
def triangleLift {a b c : V} (h : {a,b,c} ∈ K.faces) (g : G) : C(Triangle,v.TotalSpace) :=
  (v.faceLift h (a:=a) (by simp) g).comp (trianglePoint h)

lemma triangleLift_bottom {a b c : V} (h : {a,b,c} ∈ K.faces) (g : G) (s : I) :
    v.triangleLift h g (quotient (s,0)) =
      v.edgeLift (edge_of_subset K h (by simp) (by simp) : {a,b} ∈ K.faces) g s := by
  change v.inChart a _ g = v.inChart a _ g
  rw [trianglePoint_bottom]
  rfl
lemma triangleLift_left {a b c : V} (h : {a,b,c} ∈ K.faces) (g : G) (s : I) :
    v.triangleLift h g (quotient (0,s)) =
      v.edgeLift (edge_of_subset K h (by simp) (by simp) : {a,c} ∈ K.faces) g s := by
  change v.inChart a _ g = v.inChart a _ g
  rw [trianglePoint_left]
  rfl
lemma triangleLift_right {a b c : V} (h : {a,b,c} ∈ K.faces) (g : G) (s : I) :
    v.triangleLift h g (quotient (1,s)) =
      v.edgeLift (edge_of_subset K h (by simp) (by simp) : {b,c} ∈ K.faces) (g*v.value a b) s := by
  rw [edgeLift_apply,←trianglePoint_right h]
  exact (v.inChart_change_face h (a:=a) (b:=b) (by simp) (by simp) (trianglePoint h (quotient (1,s))) g).symm

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
