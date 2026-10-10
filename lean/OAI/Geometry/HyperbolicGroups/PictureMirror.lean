import Mathlib
import OAI.Geometry.HyperbolicGroups.BoundaryList

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

lemma cycles_inverse (p : Perm D) : cycles p⁻¹ = cycles p := by
  simp only [cycles,defect,support_inv,cycleType_inv]

lemma cycles_conjugate (p q : Perm D) : cycles (q*p*q⁻¹) = cycles p := by
  simp only [cycles,defect,card_support_conj,cycleType_conj]

namespace IsBoundary
variable {f : Perm D} {xs : List D} (h : IsBoundary f xs)
include h
omit [Fintype D] in
lemma reverse : IsBoundary f⁻¹ xs.reverse := by
  refine ⟨by simpa using h.nodup,?_⟩
  intro x hx
  rw [List.formPerm_reverse]
  have hx' : x ∈ xs := List.mem_reverse.mp hx
  have hy : xs.formPerm⁻¹ x ∈ xs := by
    apply List.mem_of_formPerm_apply_mem
    simpa only [Perm.inv_def,Equiv.apply_symm_apply] using hx'
  apply f.injective
  rw [Perm.inv_def,Equiv.apply_symm_apply,h.turn _ hy,Perm.inv_def,Equiv.apply_symm_apply]
end IsBoundary

namespace PictureMap
variable (M : PictureMap D)

/-- Reflection reverses every face orientation; side pairs are unchanged. -/
def mirror : PictureMap D where
  face := M.face⁻¹
  edge := M.edge
  edge_sq := M.edge_sq
  edge_ne := M.edge_ne

omit [DecidableEq D] in
lemma mirror_components : M.mirror.components = M.components := by
  apply le_antisymm
  · apply M.mirror.components_le
    · intro x
      exact M.face_le_components ((SameCycle.rfl (f := M.face⁻¹) (x := x)).apply_right.of_inv)
    · intro x
      exact M.edge_le_components (SameCycle.rfl (f := M.edge) (x := x)).apply_right
  · apply M.components_le
    · intro x
      exact M.mirror.face_le_components ((SameCycle.rfl (f := M.face) (x := x)).apply_right.inv)
    · intro x
      exact M.mirror.edge_le_components (SameCycle.rfl (f := M.edge) (x := x)).apply_right

lemma mirror_euler : M.mirror.euler = M.euler := by
  have hi : M.edge⁻¹ = M.edge := by
    apply inv_eq_of_mul_eq_one_left
    exact M.edge_sq
  have hv : M.mirror.vertex = M.edge * M.vertex⁻¹ * M.edge⁻¹ := by
    simp only [vertex,mirror,mul_inv_rev,hi,mul_assoc]
    rw [← mul_assoc M.edge M.edge,M.edge_sq,one_mul]
  rw [euler,euler,hv,cycles_conjugate,cycles_inverse]
  change cycles M.vertex + cycles M.face⁻¹ - _ = _
  rw [cycles_inverse]

lemma mirror_genusZero (h : M.GenusZero) : M.mirror.GenusZero := by
  change M.mirror.euler = _
  rw [M.mirror_euler,M.mirror_components]
  exact h

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
