import Mathlib
import OAI.Geometry.HyperbolicGroups.VoltageClosedCells
import OAI.Geometry.HyperbolicGroups.FinitePolyhedronPathAlgebra

namespace OAI

/-! Literal oriented edges and triangles of the genuine voltage cover. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

def vertexLift (a : V) (g : G) : v.TotalSpace := (v.vertexFiber a g).val
@[simp] lemma vertexLift_proj (a : V) (g : G) : v.proj (v.vertexLift a g) = vertex K a := rfl
@[simp] lemma vertexLift_coordinate (a : V) (g : G) : v.coordinate (v.vertexLift a g) = g := rfl
lemma inChart_vertex (a b : V) (g : G) :
    v.inChart a (vertex K b) g = v.vertexLift b (g * v.value a b) := by
  apply v.totalSpace_ext
  · rfl
  · simp [indexAt_vertex]

variable {v}
def edgePoint {a b : V} (h : {a,b} ∈ K.faces) : C(I,closedFace (K := K) {a,b}) where
  toFun t := ⟨edgePath K h t,
    straight_mem_face K (straight_in_face K h _ _ (vertex_mem_simplex K (by simp)) (vertex_mem_simplex K (by simp))) (vertex_mem_simplex K (by simp)) (vertex_mem_simplex K (by simp)) t⟩
  continuous_toFun := (edgePath K h).continuous.subtype_mk _
variable (v)

def edgeLift {a b : V} (h : {a,b} ∈ K.faces) (g : G) :
    Path (v.vertexLift a g) (v.vertexLift b (g * v.value a b)) where
  toFun t := v.faceLift h (a:=a) (by simp) g (edgePoint h t)
  continuous_toFun := (v.faceLift h (a:=a) (by simp) g).continuous.comp (edgePoint h).continuous
  source' := by
    change v.inChart a (edgePath K h 0) g = _
    rw [Path.source,inChart_vertex,v.self,mul_one]
  target' := by
    change v.inChart a (edgePath K h 1) g = _
    rw [Path.target,inChart_vertex]

@[simp] lemma edgeLift_proj {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t : I) :
    v.proj (v.edgeLift h g t) = edgePath K h t := rfl
@[simp] lemma edgeLift_apply {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t : I) :
    v.edgeLift h g t = v.inChart a (edgePath K h t) g := rfl

lemma edgePath_reverse {a b : V} (h : {a,b} ∈ K.faces) (t : I) :
    edgePath K (show {b,a} ∈ K.faces by simpa [Finset.pair_comm] using h) t =
      edgePath K h (unitInterval.symm t) := by
  apply Subtype.ext
  change AffineMap.lineMap (vertex K b).val (vertex K a).val (t : ℝ) =
    AffineMap.lineMap (vertex K a).val (vertex K b).val (1-(t:ℝ))
  exact AffineMap.lineMap_apply_one_sub _ _ _ |>.symm

lemma edgeLift_reverse {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t : I) :
    v.edgeLift (show {b,a} ∈ K.faces by simpa [Finset.pair_comm] using h)
      (g * v.value a b) t = v.edgeLift h g (unitInterval.symm t) := by
  rw [edgeLift_apply,edgeLift_apply,edgePath_reverse]
  exact v.inChart_change_face h (a:=a) (b:=b) (by simp) (by simp) (edgePoint h (unitInterval.symm t)) g

lemma edgeLift_self (a : V) (g : G) (t : I) :
    v.edgeLift (edge_self K a) g t = v.vertexLift a g := by
  rw [edgeLift_apply,edgePath_self]
  change v.inChart a (vertex K a) g = _
  rw [inChart_vertex,v.self,mul_one]

lemma edgeLift_deck {a b : V} (h : {a,b} ∈ K.faces) (g d : G) (t : I) :
    v.edgeLift h (d*g) t = d • v.edgeLift h g t := by
  apply v.totalSpace_ext
  · rfl
  · simp [edgeLift_apply,mul_assoc]

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
