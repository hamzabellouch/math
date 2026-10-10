import Mathlib
import OAI.Geometry.HyperbolicGroups.MappedPicture
import OAI.Geometry.HyperbolicGroups.PermErasePair

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
namespace PictureMap
variable (M : PictureMap D) (a : D)

omit [DecidableEq D] [Fintype D] in
lemma eraseEdge_invariant (x : D) :
    OffPair a (M.edge a) (M.edge x) ↔ OffPair a (M.edge a) x := by
  have h₁ : M.edge x = a ↔ x = M.edge a := by
    constructor
    · intro h; simpa only [M.edge_edge] using congrArg M.edge h
    · intro h; rw [h,M.edge_edge]
  have h₂ : M.edge x = M.edge a ↔ x = a := M.edge.apply_eq_iff_eq
  simp only [OffPair,ne_eq,h₁,h₂,and_comm]

/-- Deletion of an actual paired edge: its incident face boundaries are
spliced and the two indexed sides erased. No label or surface premise is
hidden in this finite permutation construction. -/
def eraseEdge : PictureMap {x // OffPair a (M.edge a) x} where
  face := erasePair (M.face * swap a (M.edge a)) (M.edge_ne a).symm
  edge := M.edge.subtypePerm (M.eraseEdge_invariant a)
  edge_sq := by ext x; change M.edge (M.edge x.val) = x.val; exact M.edge_edge _
  edge_ne := fun x he => M.edge_ne x.val (congrArg Subtype.val he)

omit [Fintype D] in
lemma eraseEdge_vertex (x : {x // OffPair a (M.edge a) x}) :
    ((M.eraseEdge a).vertex x).val = (erasePair M.vertex (M.edge_ne a).symm x).val := by
  change bypassPair (M.face * swap a (M.edge a)) a (M.edge a) (M.edge x.val) =
    bypassPair M.vertex a (M.edge a) x.val
  have hx := (M.eraseEdge_invariant a x.val).mpr x.property
  rw [bypassPair,bypassPair,bypass_away _ _ _ hx.2,bypass_away _ _ _ x.property.2,
    bypass_away _ _ _ hx.1,bypass_away _ _ _ x.property.1]
  simp only [vertex,mul_apply,swap_apply_of_ne_of_ne hx.1 hx.2,swap_apply_left]
  have hh : bypass (M.face * swap a (M.edge a)) a (M.edge a) =
      bypass (M.face * M.edge) a (M.edge a) := by
    simp only [bypass_away _ _ _ (M.edge_ne a),mul_apply,swap_apply_right,
      swap_apply_left,M.edge_edge]
  rw [hh]

lemma eraseEdge_face_orbits (x y : {x // OffPair a (M.edge a) x}) :
    (M.eraseEdge a).face.SameCycle x y ↔
      (M.face * swap a (M.edge a)).SameCycle x.val y.val :=
  erasePair_orbits _ (M.edge_ne a).symm _ _

omit [Fintype D] in
lemma eraseEdge_vertex_perm : (M.eraseEdge a).vertex =
    erasePair M.vertex (M.edge_ne a).symm := by
  ext x
  exact M.eraseEdge_vertex a x

end PictureMap
end HyperbolicObstruction.PictureSwitch
end

end OAI
