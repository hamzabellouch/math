import Mathlib
import OAI.Geometry.HyperbolicGroups.VoltagePrismGluing
import OAI.Geometry.HyperbolicGroups.VoltageFacePrisms
import OAI.Geometry.HyperbolicGroups.VoltageTriangleContraction
import OAI.Geometry.HyperbolicGroups.PolygonTriangleCochains
import OAI.Geometry.HyperbolicGroups.PolygonTriangles

namespace OAI

/-! A global continuous contraction of the literal polygon voltage cover,
constructed by cochain correction and locally finite closed-cell gluing. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)
  [SimplyConnectedSpace v.TotalSpace] (z : v.TotalSpace)
  (L : G → V → V → v.LoopClass z)

def correctedEdgePrisms : v.EdgePrisms z where
  H := v.correctedEdge z L
  initial := v.correctedEdge_initial z L
  final := v.correctedEdge_final z L
  agree := v.correctedEdge_agree z L

variable (hs : ∀ g a, L g a a = 1)
  (hr : ∀ {a b}, {a,b} ∈ K.faces → ∀ g, L (g*v.value a b) b a = (L g a b)⁻¹)
  {a b c : V} (h : {a,b,c} ∈ K.faces) (hi : Function.Injective ![a,b,c])
  (hL : ∀ g, L g a c * v.triangleObstruction z h g = L g a b * L (g*v.value a b) b c)

def correctedFacePrism : v.FacePrism z (v.correctedEdgePrisms z L) {a,b,c} h :=
  v.triangleFacePrism z (v.correctedEdgePrisms z L) h hi
    (fun g => v.correctedTriangle z L hs hr h g (hL g))
    (fun g => v.correctedTriangle_initial z L hs hr h g (hL g))
    (fun g => v.correctedTriangle_final z L hs hr h g (hL g))
    (fun g => v.correctedTriangle_bottom z L hs hr h g (hL g))
    (fun g => v.correctedTriangle_left z L hs hr h g (hL g))
    (fun g => v.correctedTriangle_right z L hs hr h g (hL g))
end HyperbolicObstruction.FinitePolyhedron.Voltage

namespace HyperbolicObstruction.FinitePolygonModel.Data
open FinitePolyhedron FinitePolyhedron.Voltage
variable {V E C G : Type*} [Fintype V] [Fintype E] [Fintype C]
  [DecidableEq V] [DecidableEq E] [DecidableEq C] [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (P : Data V E C) (ρ : E → G)
  (hc : ∀ c, (List.ofFn (fun i => signed ρ (P.side c i))).prod = 1)
  [LinearOrder P.Vertex] [SimplyConnectedSpace (P.voltage ρ hc).TotalSpace]
  (z : (P.voltage ρ hc).TotalSpace)

local instance : CommGroup ((P.voltage ρ hc).LoopClass z) := HSpaceFundamental.commGroup

def obstructionWeight (g : G) (q : P.Position) (j : Fin 3) : Additive ((P.voltage ρ hc).LoopClass z) :=
  Additive.ofMul ((P.voltage ρ hc).triangleObstruction z (P.collar_mem q j) g)

variable (w : G × E → Additive ((P.voltage ρ hc).LoopClass z))

def obstructionCochain (g : G) (a b : P.Vertex) : (P.voltage ρ hc).LoopClass z :=
  Additive.toMul (P.triangleCochain ρ w (P.obstructionWeight ρ hc z) g a b)

lemma obstructionCochain_self (g : G) (a : P.Vertex) : P.obstructionCochain ρ hc z w g a a = 1 := by
  apply Additive.ofMul.injective
  exact P.liftedCochain_self ρ w _ _ _ g a
lemma obstructionCochain_reverse {a b : P.Vertex} (_ : {a,b} ∈ P.complex.faces) (g : G) :
    P.obstructionCochain ρ hc z w (g*(P.voltage ρ hc).value a b) b a =
      (P.obstructionCochain ρ hc z w g a b)⁻¹ := by
  apply Additive.ofMul.injective
  exact P.liftedCochain_reverse ρ w _ _ _ g a b

variable (hw : ∀ d c, (∑ i : Fin (P.size c),
    signedCochain ρ w (d*((List.ofFn (fun i => signed ρ (P.side c i))).take i.val).prod) (P.side c i)) =
    ∑ i : Fin (P.size c), ∑ j : Fin 3,
      P.triangleWeight (P.obstructionWeight ρ hc z) (d*P.cornerOffset ρ ⟨c,(i,j)⟩) ⟨c,(i,j)⟩)
include hw in
lemma obstructionCochain_triangle (q : P.Position) (j : Fin 3) (g : G) :
    P.obstructionCochain ρ hc z w g (P.outer q) (P.collarC q j) *
      (P.voltage ρ hc).triangleObstruction z (P.collar_mem q j) g =
    P.obstructionCochain ρ hc z w g (P.outer q) (P.collarB q j) *
      P.obstructionCochain ρ hc z w (g*(P.voltage ρ hc).value (P.outer q) (P.collarB q j))
        (P.collarB q j) (P.collarC q j) := by
  have hh := P.triangleCochain_coboundary ρ w (P.obstructionWeight ρ hc z) hc hw g q
  apply Additive.ofMul.injective
  change P.triangleCochain ρ w (P.obstructionWeight ρ hc z) g (P.outer q) (P.collarC q j) +
      P.obstructionWeight ρ hc z g q j =
    P.triangleCochain ρ w (P.obstructionWeight ρ hc z) g (P.outer q) (P.collarB q j) +
      P.triangleCochain ρ w (P.obstructionWeight ρ hc z)
        (g*P.value ρ (P.outer q) (P.collarB q j)) (P.collarB q j) (P.collarC q j)
  fin_cases j
  · change _ + P.obstructionWeight ρ hc z g q 0 = _
    rw [add_comm _ (P.obstructionWeight ρ hc z g q 0)]
    exact (eq_add_of_sub_eq hh.1).symm
  · change _ + P.obstructionWeight ρ hc z g q 1 = _
    rw [add_comm _ (P.obstructionWeight ρ hc z g q 1)]
    exact (eq_add_of_sub_eq hh.2.1).symm
  · change _ + P.obstructionWeight ρ hc z g q 2 = _
    rw [add_comm _ (P.obstructionWeight ρ hc z g q 2)]
    exact (eq_add_of_sub_eq hh.2.2).symm

def contractionFace (q : P.Position) (j : Fin 3) :
    (P.voltage ρ hc).FacePrism z
      ((P.voltage ρ hc).correctedEdgePrisms z (P.obstructionCochain ρ hc z w))
      {P.outer q,P.collarB q j,P.collarC q j} (P.collar_mem q j) :=
  (P.voltage ρ hc).correctedFacePrism z (P.obstructionCochain ρ hc z w)
    (P.obstructionCochain_self ρ hc z w) (P.obstructionCochain_reverse ρ hc z w)
    (P.collar_mem q j) (P.collar_injective q j) (P.obstructionCochain_triangle ρ hc z w hw q j)

include hw in
lemma threeFacePrism (s : Finset P.Vertex) (hs : s ∈ P.complex.faces) (h3 : s.card = 3) :
    Nonempty ((P.voltage ρ hc).FacePrism z
      ((P.voltage ρ hc).correctedEdgePrisms z (P.obstructionCochain ρ hc z w)) s hs) := by
  obtain ⟨q,j,hq⟩ := P.three_face_collar hs h3
  rw [P.collarFace_eq] at hq
  subst s
  exact ⟨P.contractionFace ρ hc z w hw q j⟩

def coverContraction : C(I × (P.voltage ρ hc).TotalSpace,(P.voltage ρ hc).TotalSpace) :=
  (P.voltage ρ hc).fromTrianglePrisms z
    ((P.voltage ρ hc).correctedEdgePrisms z (P.obstructionCochain ρ hc z w))
    (fun _ hs => P.simplex_card_le_three hs) (P.threeFacePrism ρ hc z w hw)
lemma coverContraction_initial (e : (P.voltage ρ hc).TotalSpace) :
    P.coverContraction ρ hc z w hw (0,e) = e :=
  (P.voltage ρ hc).fromTrianglePrisms_initial _ _ _ _ e
lemma coverContraction_final (e : (P.voltage ρ hc).TotalSpace) :
    P.coverContraction ρ hc z w hw (1,e) = z :=
  (P.voltage ρ hc).fromTrianglePrisms_final _ _ _ _ e

lemma coverContraction_fixed (a : P.Vertex) (g : G)
    (he : (P.voltage ρ hc).vertexLift a g = z) (t : I) :
    P.coverContraction ρ hc z w hw (t,z) = z := by
  have hz : (P.voltage ρ hc).edgeLift (edge_self P.complex a) g 0 = z :=
    ((P.voltage ρ hc).edgeLift_self a g 0).trans he
  calc
    P.coverContraction ρ hc z w hw (t,z) =
        P.coverContraction ρ hc z w hw (t,(P.voltage ρ hc).edgeLift (edge_self P.complex a) g 0) :=
      congrArg (fun e => P.coverContraction ρ hc z w hw (t,e)) hz.symm
    _ = z := by
      rw [coverContraction,(P.voltage ρ hc).fromTrianglePrisms_edge]
      exact (P.voltage ρ hc).correctedEdge_fixed z (P.obstructionCochain ρ hc z w) a g he t 0

end HyperbolicObstruction.FinitePolygonModel.Data
end

end OAI
