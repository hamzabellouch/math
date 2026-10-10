import Mathlib
import OAI.Geometry.HyperbolicGroups.FinitePolyhedronPathAlgebra
import OAI.Geometry.HyperbolicGroups.EdgeCoordinates
import OAI.Geometry.HyperbolicGroups.VoltageGraphHomotopy

namespace OAI

/-! Gluing of edge data is proved from the literal lifted coordinates. No
agreement of independent choices on intersecting edges is assumed. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

lemma vertexLift_eq_iff (a b : V) (g d : G) :
    v.vertexLift a g = v.vertexLift b d ↔ a = b ∧ g = d := by
  refine ⟨fun h => ⟨vertex_injective K (congrArg v.proj h),congrArg v.coordinate h⟩,?_⟩
  rintro ⟨rfl,rfl⟩; rfl
lemma edgeLift_sheet_injective {a b : V} (h : {a,b} ∈ K.faces) (s : I) :
    Function.Injective (fun g => v.edgeLift h g s) := by
  intro g d he
  have hh := congrArg v.coordinate he
  change g*v.value a (v.core.indexAt (edgePath K h s)) = d*v.value a (v.core.indexAt (edgePath K h s)) at hh
  exact mul_right_cancel hh

variable {X : Type*}
structure EdgeData where
  vertex : V → G → I → X
  edge : ∀ {a b : V}, {a,b} ∈ K.faces → G → I → I → X
  left : ∀ {a b : V} (h : {a,b} ∈ K.faces) g t, edge h g t 0 = vertex a g t
  right : ∀ {a b : V} (h : {a,b} ∈ K.faces) g t, edge h g t 1 = vertex b (g*v.value a b) t
  collapsed : ∀ a g t s, edge (edge_self K a) g t s = vertex a g t
  reversed : ∀ {a b : V} (h : {a,b} ∈ K.faces) g t s,
    edge (show {b,a} ∈ K.faces by simpa [Finset.pair_comm] using h) (g*v.value a b) t s =
      edge h g t (unitInterval.symm s)

namespace EdgeData
variable {v} (H : v.EdgeData (X := X))
lemma at_vertex {a b c : V} (h : {a,b} ∈ K.faces) (g d : G) (t s : I)
    (he : v.edgeLift h g s = v.vertexLift c d) : H.edge h g t s = H.vertex c d t := by
  by_cases hab : a = b
  · subst b
    rw [v.edgeLift_self] at he
    obtain ⟨rfl,rfl⟩ := (v.vertexLift_eq_iff a c g d).mp he
    exact H.collapsed _ _ _ _
  have hp := congrArg v.proj he
  obtain ⟨rfl,hac⟩|⟨rfl,hbc⟩ := edgePath_eq_vertex_cases K h hab s hp
  · rw [Path.source] at he
    obtain ⟨rfl,rfl⟩ := (v.vertexLift_eq_iff a c g d).mp he
    exact H.left _ _ _
  · rw [Path.target] at he
    obtain ⟨rfl,rfl⟩ := (v.vertexLift_eq_iff b c (g*v.value a b) d).mp he
    exact H.right _ _ _

lemma agree {a b c d : V} (h : {a,b} ∈ K.faces) (h' : {c,d} ∈ K.faces)
    (g k : G) (t s r : I) (he : v.edgeLift h g s = v.edgeLift h' k r) :
    H.edge h g t s = H.edge h' k t r := by
  by_cases hab : a = b
  · subst b
    rw [H.collapsed]
    exact (H.at_vertex h' k g t r (he.symm.trans (v.edgeLift_self a g s))).symm
  by_cases hcd : c = d
  · subst d
    rw [H.collapsed]
    exact H.at_vertex h g k t s (he.trans (v.edgeLift_self c k r))
  by_cases hs0 : s = 0
  · subst s
    rw [H.left]
    exact (H.at_vertex h' k g t r (he.symm.trans (Path.source _))).symm
  by_cases hs1 : s = 1
  · subst s
    rw [H.right]
    exact (H.at_vertex h' k (g*v.value a b) t r (he.symm.trans (Path.target _))).symm
  have hp := congrArg v.proj he
  obtain ⟨hac,hbd,hst⟩|⟨had,hbc,hst⟩ := edgePath_eq_edge_interior K h h' hab hcd s r hs0 hs1 hp
  · subst c; subst d; subst r
    have hg : g = k := v.edgeLift_sheet_injective h s he
    subst k; rfl
  · subst d; subst c; subst s
    rw [←v.edgeLift_reverse h g r] at he
    have hg : g*v.value a b = k := v.edgeLift_sheet_injective h' r he
    subst k
    exact (H.reversed h g t r).symm
end EdgeData

variable [LinearOrder V] [SimplyConnectedSpace v.TotalSpace] (z : v.TotalSpace)
def graphEdgeData : v.EdgeData (X := v.TotalSpace) where
  vertex a g t := v.vertexTrack z a g t
  edge h g t s := v.edgeHomotopy z h g (t,s)
  left := v.edgeHomotopy_left z
  right := v.edgeHomotopy_right z
  collapsed a g t s := by simp only [edgeHomotopy,ite_true,eq_self]; rfl
  reversed := v.edgeHomotopy_reverse z

lemma edgeHomotopy_agree {a b c d : V} (h : {a,b} ∈ K.faces) (h' : {c,d} ∈ K.faces)
    (g k : G) (t s r : I) (he : v.edgeLift h g s = v.edgeLift h' k r) :
    v.edgeHomotopy z h g (t,s) = v.edgeHomotopy z h' k (t,r) :=
  (v.graphEdgeData z).agree h h' g k t s r he

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
