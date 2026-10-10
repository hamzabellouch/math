import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.PermEuler
import OAI.Geometry.HyperbolicGroups.PictureEuler

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
namespace PictureMap
variable (M : PictureMap D)

/-- The vertices of the actual rotation system, without collapsing darts or
parallel edge copies. Only the associated simple adjacency ignores loops. -/
abbrev GraphVertex := Quotient (SameCycle.setoid M.vertex)

def vertexClass (x : D) : M.GraphVertex := Quotient.mk _ x

omit [DecidableEq D] [Fintype D] in
lemma vertexClass_eq_iff (x y : D) :
    M.vertexClass x = M.vertexClass y ↔ M.vertex.SameCycle x y :=
  Quotient.eq

/-- The underlying simple graph used in the planar-separator argument.
Its adjacency is induced by real edge copies of the rotation system. -/
def underlyingGraph : SimpleGraph M.GraphVertex where
  Adj v w := v ≠ w ∧ ∃ x : D, M.vertexClass x = v ∧ M.vertexClass (M.edge x) = w
  symm := ⟨by
    rintro v w ⟨hne,x,hx,he⟩
    exact ⟨hne.symm,M.edge x,he,by rw [M.edge_edge]; exact hx⟩⟩
  loopless := ⟨by rintro v ⟨h,_⟩; exact h rfl⟩

omit [DecidableEq D] [Fintype D] in
lemma underlying_adj_iff (v w : M.GraphVertex) :
    M.underlyingGraph.Adj v w ↔ v ≠ w ∧ ∃ x : D,
      M.vertexClass x = v ∧ M.vertexClass (M.edge x) = w := Iff.rfl

omit [DecidableEq D] in
/-- Distinct neighbors inject into actual incident darts. This is the exact
reason the multigraph valence bound also bounds the underlying simple degree. -/
theorem underlying_neighbor_card_le (v : M.GraphVertex) :
    Nat.card (M.underlyingGraph.neighborSet v) ≤ Nat.card {x : D // M.vertexClass x = v} := by
  let f : M.underlyingGraph.neighborSet v → {x : D // M.vertexClass x = v} := fun w =>
    ⟨w.property.2.choose,w.property.2.choose_spec.1⟩
  apply Nat.card_le_card_of_injective f
  intro a b hab
  apply Subtype.ext
  have hx : (f a).val = (f b).val := congrArg Subtype.val hab
  exact a.property.2.choose_spec.2.symm.trans
    ((congrArg (fun x => M.vertexClass (M.edge x)) hx).trans b.property.2.choose_spec.2)

def vertex_fiber_equiv (x : D) :
    {y : D // M.vertexClass y = M.vertexClass x} ≃ {y : D // M.vertex.SameCycle x y} :=
  Equiv.subtypeEquivRight fun y => (M.vertexClass_eq_iff y x).trans sameCycle_comm

lemma underlying_neighbor_card_le_cycle (x : D) :
    Nat.card (M.underlyingGraph.neighborSet (M.vertexClass x)) ≤
      Fintype.card {y : D // M.vertex.SameCycle x y} := by
  have h := M.underlying_neighbor_card_le (M.vertexClass x)
  rw [Nat.card_congr (M.vertex_fiber_equiv x)] at h
  simpa only [Nat.card_eq_fintype_card] using h

omit [DecidableEq D] in
lemma components_le_underlying_reachable :
    M.components ≤ Setoid.comap M.vertexClass M.underlyingGraph.reachableSetoid := by
  apply sup_le
  · intro x y h
    change M.underlyingGraph.Reachable (M.vertexClass x) (M.vertexClass y)
    rw [(M.vertexClass_eq_iff x y).mpr h]
  · apply sameCycle_le_of_apply
    intro x
    change M.underlyingGraph.Reachable (M.vertexClass x) (M.vertexClass (M.edge x))
    by_cases h : M.vertexClass x = M.vertexClass (M.edge x)
    · rw [h]
    · exact SimpleGraph.Adj.reachable ⟨h,x,rfl,rfl⟩

/-- Sending each rotation vertex to its true connected component. -/
def graphComponent : M.GraphVertex → Quotient M.components :=
  Quotient.map id (fun _ _ h => M.vertex_le_components h)

omit [DecidableEq D] [Fintype D] in
lemma graphComponent_adj {v w : M.GraphVertex} (h : M.underlyingGraph.Adj v w) :
    M.graphComponent v = M.graphComponent w := by
  obtain ⟨hne,x,rfl,rfl⟩ := h
  exact Quotient.sound (M.edge_le_components SameCycle.rfl.apply_right)

omit [DecidableEq D] [Fintype D] in
lemma graphComponent_reachable {v w : M.GraphVertex} (h : M.underlyingGraph.Reachable v w) :
    M.graphComponent v = M.graphComponent w := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h p ih => exact (M.graphComponent_adj h).trans ih

omit [DecidableEq D] in
/-- Simple-graph reachability is exactly connectivity of the actual side
identifications, not an additional assumption about a planar drawing. -/
theorem underlying_reachable_iff (x y : D) :
    M.underlyingGraph.Reachable (M.vertexClass x) (M.vertexClass y) ↔ M.components x y := by
  constructor
  · intro h
    exact Quotient.exact (M.graphComponent_reachable h)
  · intro h; exact M.components_le_underlying_reachable h

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
