import Mathlib
import OAI.Geometry.HyperbolicGroups.FinitePolyhedronPathAlgebra
import OAI.Geometry.HyperbolicGroups.TriangleHomotopyExtension
import OAI.Geometry.HyperbolicGroups.VoltageGraphHomotopy
import OAI.Geometry.HyperbolicGroups.VoltageTriangles

namespace OAI

/-! Extend the SAME coherent lifted graph contraction over each actual closed
triangle. Its terminal map is based along all three sides. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open TriangleSquare SquareBoundaryExtension TriangleHomotopyExtension
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)
  [SimplyConnectedSpace v.TotalSpace] (z : v.TotalSpace)

omit [Fintype V] [LinearOrder V] [TopologicalSpace G] [DiscreteTopology G]
    [SimplyConnectedSpace v.TotalSpace] in
lemma triangle_voltage {a b c : V} (h : {a,b,c} ∈ K.faces) (g : G) :
    (g*v.value a b)*v.value b c = g*v.value a c := by
  rw [mul_assoc,v.triangle a b c h]

variable {a b c : V} (h : {a,b,c} ∈ K.faces) (g : G)
def triangleSides : SquareBoundaryExtension.Data (X := v.TotalSpace) where
  side q := if q.1 = 0 then
      if q.2 then v.edgeHomotopy z (edge_of_subset K h (by simp) (by simp) : {b,c} ∈ K.faces) (g*v.value a b)
      else v.edgeHomotopy z (edge_of_subset K h (by simp) (by simp) : {a,c} ∈ K.faces) g
    else if q.2 then (v.vertexTrack z c (g*v.value a c)).toContinuousMap.comp ⟨Prod.fst,continuous_fst⟩
      else v.edgeHomotopy z (edge_of_subset K h (by simp) (by simp) : {a,b} ∈ K.faces) g
  corner t i j := by
    cases i <;> cases j <;> dsimp [endpoint]
    · rw [v.edgeHomotopy_left,v.edgeHomotopy_left]
    · rw [v.edgeHomotopy_right]
    · rw [v.edgeHomotopy_left,v.edgeHomotopy_right]
    · rw [v.edgeHomotopy_right,v.triangle_voltage h]

lemma triangleSides_initial (q : Fin 2 × Bool) (w : Fin 2 → I)
    (hw : w q.1 = endpoint q.2) :
    (v.triangleSides z h g).side q (0,w (other q.1)) = v.triangleLift h g (quotient (pairCube w)) := by
  rcases q with ⟨i,j⟩
  fin_cases i <;> cases j <;> dsimp [triangleSides,other,pairCube,endpoint] at hw ⊢
  · change v.edgeHomotopy z _ g (0,w 1) = v.triangleLift h g (quotient (w 0,w 1))
    rw [v.edgeHomotopy_initial,hw,v.triangleLift_left]
  · change v.edgeHomotopy z _ (g*v.value a b) (0,w 1) = v.triangleLift h g (quotient (w 0,w 1))
    rw [v.edgeHomotopy_initial,hw,v.triangleLift_right]
  · change v.edgeHomotopy z _ g (0,w 0) = v.triangleLift h g (quotient (w 0,w 1))
    rw [v.edgeHomotopy_initial,hw,v.triangleLift_bottom]
  · rw [Path.source]
    change v.vertexLift c (g*v.value a c) = v.triangleLift h g (quotient (w 0,w 1))
    rw [hw,quotient_one,←quotient_one (1:I),v.triangleLift_right,Path.target,v.triangle_voltage h]

lemma triangleSides_top (t s : I) :
    (v.triangleSides z h g).side (1,true) (t,s) = (v.triangleSides z h g).side (1,true) (t,0) := rfl

def triangleHomotopy : C(I × Triangle,v.TotalSpace) :=
  TriangleHomotopyExtension.extend (v.triangleLift h g) (v.triangleSides z h g)
    (v.triangleSides_initial z h g) (v.triangleSides_top z h g)

lemma triangleHomotopy_initial (w : Triangle) : v.triangleHomotopy z h g (0,w) = v.triangleLift h g w :=
  TriangleHomotopyExtension.extend_initial _ _ _ _ w
lemma triangleHomotopy_bottom (t s : I) :
    v.triangleHomotopy z h g (t,quotient (s,0)) =
    v.edgeHomotopy z (edge_of_subset K h (by simp) (by simp) : {a,b} ∈ K.faces) g (t,s) :=
  TriangleHomotopyExtension.extend_bottom _ _ _ _ t s
lemma triangleHomotopy_left (t s : I) :
    v.triangleHomotopy z h g (t,quotient (0,s)) =
    v.edgeHomotopy z (edge_of_subset K h (by simp) (by simp) : {a,c} ∈ K.faces) g (t,s) :=
  TriangleHomotopyExtension.extend_left _ _ _ _ t s
lemma triangleHomotopy_right (t s : I) :
    v.triangleHomotopy z h g (t,quotient (1,s)) =
    v.edgeHomotopy z (edge_of_subset K h (by simp) (by simp) : {b,c} ∈ K.faces) (g*v.value a b) (t,s) :=
  TriangleHomotopyExtension.extend_right _ _ _ _ t s

def basedTriangle : C(Triangle,v.TotalSpace) := (v.triangleHomotopy z h g).comp ⟨fun w => (1,w),by fun_prop⟩
lemma basedTriangle_bottom (s : I) : v.basedTriangle z h g (quotient (s,0)) = z := by
  change v.triangleHomotopy z h g (1,_) = _
  rw [v.triangleHomotopy_bottom,v.edgeHomotopy_final]
lemma basedTriangle_left (s : I) : v.basedTriangle z h g (quotient (0,s)) = z := by
  change v.triangleHomotopy z h g (1,_) = _
  rw [v.triangleHomotopy_left,v.edgeHomotopy_final]
lemma basedTriangle_right (s : I) : v.basedTriangle z h g (quotient (1,s)) = z := by
  change v.triangleHomotopy z h g (1,_) = _
  rw [v.triangleHomotopy_right,v.edgeHomotopy_final]

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
