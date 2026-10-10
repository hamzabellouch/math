import Mathlib
import OAI.Geometry.HyperbolicGroups.SubpairingCopies

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]
variable (M : PictureMap D) (q : Perm D) (hq : ∀ x, q x = x ∨ q x = M.edge x)
variable (hG : M.GenusZero) (hspan : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤)
variable (hboundary : cycles (M.vertex*q) = 1)

omit [DecidableEq D] [Nonempty D] in
lemma retained_contact_edge_of_covers (x : D) (a : M.RetainedContact q)
    (ha : a.val = x ∨ a.val = M.edge x) :
    M.retainedContactEdge q a = s(M.vertexClass x,M.vertexClass (M.edge x)) := by
  rcases ha with ha | ha
  · simp only [retainedContactEdge,ha]
  · simp only [retainedContactEdge,ha,M.edge_edge]
    exact Sym2.eq_swap

include hq hG hspan hboundary in
lemma tree_retained_loopless (x : D) (hx : q x ≠ x) :
    M.vertexClass x ≠ M.vertexClass (M.edge x) := by
  obtain ⟨a,ha⟩ := M.retained_contact_covers q hq x hx
  have he := (M.tree_retained_contacts_bijective q hq hG hspan hboundary).2
  have hm : s(M.vertexClass x,M.vertexClass (M.edge x)) ∈
      (M.subpairingGraph q (M.subpairing_sq q hq)).edgeFinset := by
    rw [he]
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,M.retained_contact_edge_of_covers q x a ha⟩
  have hadj : (M.subpairingGraph q (M.subpairing_sq q hq)).Adj
      (M.vertexClass x) (M.vertexClass (M.edge x)) := by simpa using hm
  exact hadj.1

include hq hG hspan hboundary in
/-- Exact oriented dart-copy uniqueness in the primal spanning tree. It is
stronger than acyclicity of the simplified graph: parallel copies cannot
be discarded before using a boundary-conservation argument. -/
theorem tree_retained_dart_unique (x y : D) (hx : q x ≠ x) (hy : q y ≠ y)
    (hv : M.vertexClass x = M.vertexClass y)
    (hw : M.vertexClass (M.edge x) = M.vertexClass (M.edge y)) : x = y := by
  obtain ⟨a,ha⟩ := M.retained_contact_covers q hq x hx
  obtain ⟨b,hb⟩ := M.retained_contact_covers q hq y hy
  have hab : a = b := (M.tree_retained_contacts_bijective q hq hG hspan hboundary).1 (by
    rw [M.retained_contact_edge_of_covers q x a ha,
      M.retained_contact_edge_of_covers q y b hb,hv,hw])
  have habv := congrArg Subtype.val hab
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact ha.symm.trans (habv.trans hb)
  · have he : x = M.edge y := ha.symm.trans (habv.trans hb)
    exact False.elim (M.tree_retained_loopless q hq hG hspan hboundary y hy
      (hv.symm.trans (congrArg M.vertexClass he)))
  · have he : M.edge x = y := ha.symm.trans (habv.trans hb)
    exact False.elim (M.tree_retained_loopless q hq hG hspan hboundary x hx
      (hv.trans (congrArg M.vertexClass he).symm))
  · exact M.edge.injective (ha.symm.trans (habv.trans hb))

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

section

end
end

end OAI
