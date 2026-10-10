import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.PictureEuler

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
namespace PictureMap
variable {D : Type*} (P : PictureMap D)

/-- Literal rotation-system duality: faces and vertices exchange, while
individual edge-side copies and their pairing are unchanged. -/
def dual : PictureMap D where
  face := P.vertex
  edge := P.edge
  edge_sq := P.edge_sq
  edge_ne := P.edge_ne

@[simp] lemma dual_edge : P.dual.edge = P.edge := rfl
@[simp] lemma dual_face : P.dual.face = P.vertex := rfl
@[simp] lemma dual_vertex : P.dual.vertex = P.face := by
  change (P.face * P.edge) * P.edge = P.face
  rw [mul_assoc,P.edge_sq,mul_one]
@[simp] lemma dual_dual : P.dual.dual = P := by
  cases P
  simp only [dual,vertex,mul_assoc]
  congr 1
  rename_i f e hs hn
  rw [hs,mul_one]

variable [Fintype D]

lemma dual_components : P.dual.components = P.components := by
  apply le_antisymm
  · apply P.dual.components_le
    · intro x
      exact P.vertex_le_components (SameCycle.rfl.apply_right)
    · intro x
      exact P.edge_le_components (SameCycle.rfl.apply_right)
  · apply P.components_le
    · intro x
      apply P.dual.vertex_le_components
      rw [P.dual_vertex]
      exact SameCycle.rfl.apply_right
    · intro x
      exact P.dual.edge_le_components (SameCycle.rfl.apply_right)

variable [DecidableEq D]

@[simp] lemma dual_euler : P.dual.euler = P.euler := by
  simp only [euler,dual_vertex,dual_face]
  omega

lemma dual_genusZero (h : P.GenusZero) : P.dual.GenusZero := by
  change P.dual.euler = 2 * (Nat.card (Quotient P.dual.components) : ℤ)
  rw [P.dual_euler,P.dual_components]
  exact h

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
