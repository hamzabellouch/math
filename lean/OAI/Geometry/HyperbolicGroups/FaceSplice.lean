import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureGenus

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

/-- Splicing oriented boundary polygons at their outgoing corners. This is
connected sum at the outside faces when the two corners are in distinct
components; no edge or side map is changed. -/
def splice (a b : D) : PictureMap D where
  face := M.face * swap a b
  edge := M.edge
  edge_sq := M.edge_sq
  edge_ne := M.edge_ne

omit [Fintype D] in
lemma splice_vertex (a b : D) :
    (M.splice a b).vertex = M.vertex * swap (M.edge a) (M.edge b) := by
  rw [vertex,splice,vertex]
  have h : swap a b * M.edge = M.edge * swap (M.edge a) (M.edge b) := by
    rw [mul_swap_eq_swap_mul,M.edge_edge,M.edge_edge]
  rw [mul_assoc,h,← mul_assoc]

lemma splice_components_le (a b : D) :
    (M.splice a b).components ≤ glue M.components a b := by
  let s := glue M.components a b
  have hs : M.components ≤ s := le_glue _ _ _
  have ht : ∀ x, s x (swap a b x) := fun x =>
    sameCycle_swap_le (glue_pair _ a b) SameCycle.rfl.apply_right
  apply (M.splice a b).components_le
  · intro x
    exact s.trans' (ht x) (hs (M.face_le_components (SameCycle.rfl (x := swap a b x)).apply_right))
  · intro x
    exact hs (M.edge_le_components SameCycle.rfl.apply_right)

lemma components_le_splice (a b : D) (h : (M.splice a b).components a b) :
    M.components ≤ (M.splice a b).components := by
  let s := (M.splice a b).components
  have ht : ∀ x, s x (swap a b x) := fun x =>
    sameCycle_swap_le h SameCycle.rfl.apply_right
  apply M.components_le
  · intro x
    have hf := (M.splice a b).face_le_components (SameCycle.rfl (x := swap a b x)).apply_right
    have he : (M.splice a b).face (swap a b x) = M.face x := by simp [splice]
    rw [he] at hf
    exact s.trans' (ht x) hf
  · intro x
    exact (M.splice a b).edge_le_components SameCycle.rfl.apply_right

/-- Two components are joined, with their actual new component equivalence
exactly the quotient gluing relation. -/
theorem splice_components (a b : D) (h : ¬ M.components a b) :
    (M.splice a b).components = glue M.components a b := by
  have hf : ¬ M.face.SameCycle a b := fun hh => h (M.face_le_components hh)
  have hn : (M.splice a b).components a b :=
    (M.splice a b).face_le_components (sameCycle_after_swap_right M.face hf)
  apply le_antisymm (M.splice_components_le a b)
  exact glue_le _ _ _ (M.components_le_splice a b hn) hn

lemma splice_euler (a b : D) (h : ¬ M.components a b) :
    (M.splice a b).euler + 2 = M.euler := by
  have hf : ¬ M.face.SameCycle a b := fun hh => h (M.face_le_components hh)
  have hv : ¬ M.vertex.SameCycle (M.edge a) (M.edge b) := by
    intro hh
    exact h (M.components.trans' (M.edge_le_components (SameCycle.rfl (x := a)).apply_right)
      (M.components.trans' (M.vertex_le_components hh)
        (M.components.symm' (M.edge_le_components (SameCycle.rfl (x := b)).apply_right))))
  have hF := cycles_merge_right M.face hf
  have hV := cycles_merge_right M.vertex hv
  rw [euler,euler,splice_vertex]
  change cycles (M.vertex * swap (M.edge a) (M.edge b)) + cycles (M.face * swap a b) - _ + 2 = _
  omega

/-- Joining two genus-zero components along the outside face preserves genus
zero. This is the finite combinatorial gluing used to assemble disk pictures. -/
theorem splice_genusZero (hM : M.GenusZero) (a b : D) (h : ¬ M.components a b) :
    (M.splice a b).GenusZero := by
  have hE := M.splice_euler a b h
  have hC := card_glue M.components a b
  rw [ite_eq_right h] at hC
  rw [← M.splice_components a b h] at hC
  change M.euler = _ at hM
  change (M.splice a b).euler = _
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
