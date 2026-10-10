import Mathlib
import OAI.Geometry.HyperbolicGroups.FaceSplice

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

lemma components_le_glue_splice (a b : D) :
    M.components ≤ glue (M.splice a b).components a b := by
  let s := glue (M.splice a b).components a b
  have hs : (M.splice a b).components ≤ s := le_glue _ _ _
  have ht : ∀ x, s x (swap a b x) := fun x =>
    sameCycle_swap_le (glue_pair _ a b) SameCycle.rfl.apply_right
  apply M.components_le
  · intro x
    have hf := hs ((M.splice a b).face_le_components (SameCycle.rfl (x := swap a b x)).apply_right)
    have he : (M.splice a b).face (swap a b x) = M.face x := by simp [splice]
    rw [he] at hf
    exact s.trans' (ht x) hf
  · intro x
    exact hs ((M.splice a b).edge_le_components SameCycle.rfl.apply_right)

lemma split_components_glue (a b : D) (hf : M.face.SameCycle a b) :
    glue (M.splice a b).components a b = M.components := by
  have hab : M.components a b := M.face_le_components hf
  have hnew : (M.splice a b).components ≤ M.components := by
    have h := M.splice_components_le a b
    rwa [glue_eq_of_rel _ _ _ hab] at h
  exact le_antisymm (glue_le _ _ _ hnew hab) (M.components_le_glue_splice a b)

lemma split_components_card (a b : D) (hf : M.face.SameCycle a b) :
    (Nat.card (Quotient (M.splice a b).components) : ℤ) =
      Nat.card (Quotient M.components) +
        if (M.splice a b).components a b then 0 else 1 := by
  have h := card_glue (M.splice a b).components a b
  rw [M.split_components_glue a b hf] at h
  omega

/-- Split a face at ANY two of its corners, identifying their endpoint
regions. Neither an embedded boundary nor distinct source endpoints is
required. If the endpoints were already equal the affected sphere can
split into two; otherwise the number of components is unchanged. -/
theorem split_genusZero (hM : M.GenusZero) (a b : D)
    (hne : a ≠ b) (hf : M.face.SameCycle a b) : (M.splice a b).GenusZero := by
  have hF := cycles_split_right M.face hne hf
  have hC := M.split_components_card a b hf
  have hV := M.splice_vertex a b
  change M.euler = _ at hM
  change (M.splice a b).euler = _
  by_cases hv : M.vertex.SameCycle (M.edge a) (M.edge b)
  · have hc := cycles_split_right M.vertex (M.edge.injective.ne hne) hv
    have hE : (M.splice a b).euler = M.euler + 2 := by
      rw [euler,euler,hV]
      change cycles (M.vertex * swap (M.edge a) (M.edge b)) + cycles (M.face * swap a b) - _ = _
      rw [hc,hF]; ring
    have he := (M.splice a b).euler_le
    split_ifs at hC <;> omega
  · have hc := cycles_merge_right M.vertex hv
    have hE : (M.splice a b).euler = M.euler := by
      rw [euler,euler,hV]
      change cycles (M.vertex * swap (M.edge a) (M.edge b)) + cycles (M.face * swap a b) - _ = _
      omega
    have hv' : (M.splice a b).vertex.SameCycle (M.edge a) (M.edge b) := by
      rw [hV]
      exact sameCycle_after_swap_right M.vertex hv
    have hsame : (M.splice a b).components a b := by
      apply (M.splice a b).components.trans' ((M.splice a b).edge_le_components (SameCycle.rfl (x := a)).apply_right)
      exact (M.splice a b).components.trans' ((M.splice a b).vertex_le_components hv')
        ((M.splice a b).components.symm' ((M.splice a b).edge_le_components (SameCycle.rfl (x := b)).apply_right))
    rw [ite_eq_left hsame] at hC
    omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
