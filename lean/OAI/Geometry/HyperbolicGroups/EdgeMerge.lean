import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMapFurther
import OAI.Geometry.HyperbolicGroups.PermErasePair

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*}
namespace PictureMap
variable (M : PictureMap D) {a b : D}

/-- The common side of two distinct, non-monogon faces. These are local
incidence hypotheses, not any normalization or genus conclusion. -/
structure MergeSide (a b : D) : Prop where
  paired : M.edge a = b
  distinct_faces : ¬ M.face.SameCycle a b
  left_nonmonogon : M.face a ≠ a
  right_nonmonogon : M.face b ≠ b

namespace MergeSide
variable {M} (h : M.MergeSide a b)
include h
lemma ne : a ≠ b := fun he => M.edge_ne a (h.paired.trans he.symm)
lemma paired_back : M.edge b = a := by rw [← h.paired,M.edge_edge]
lemma face_left_ne_right : M.face a ≠ b := by
  intro he
  exact h.distinct_faces (he ▸ (SameCycle.rfl (x := a)).apply_right)
lemma face_right_ne_left : M.face b ≠ a := by
  intro he
  exact h.distinct_faces ((he ▸ (SameCycle.rfl (x := b)).apply_right).symm)
lemma edge_invariant (x : D) : OffPair a b (M.edge x) ↔ OffPair a b x := by
  change (M.edge x ≠ a ∧ M.edge x ≠ b) ↔ (x ≠ a ∧ x ≠ b)
  have h₁ : M.edge x = a ↔ x = b := by rw [← h.paired_back]; exact M.edge.apply_eq_iff_eq
  have h₂ : M.edge x = b ↔ x = a := by rw [← h.paired]; exact M.edge.apply_eq_iff_eq
  simp only [ne_eq,h₁,h₂,and_comm]

variable [DecidableEq D]

omit h in
lemma crossed_a : (M.face * swap a b) a = M.face b := by simp
lemma crossed_b : bypass (M.face * swap a b) a b = M.face a := by
  rw [bypass_away _ _ _ h.ne.symm]
  simp only [mul_apply,swap_apply_right,ite_eq_right h.left_nonmonogon]
omit [DecidableEq D] in
lemma vertex_a : M.vertex a = M.face b := by rw [vertex,mul_apply,h.paired]
lemma vertex_b : bypass M.vertex a b = M.face a := by
  rw [bypass_away _ _ _ h.ne.symm]
  have hb : M.vertex b = M.face a := by rw [vertex,mul_apply,h.paired_back]
  rw [hb,ite_eq_right h.left_nonmonogon]

/-- The exact permutation identity underlying deletion of a shared edge:
face cycles merge; the two endpoint vertex cycles only bypass the deleted
corners. Other contacts between the faces are immaterial. -/
lemma erase_identity :
    bypassPair (M.face * swap a b) a b * (swap a b * M.edge) =
      bypassPair M.vertex a b := by
  change swap b (bypass (M.face * swap a b) a b) *
    (swap a ((M.face * swap a b) a) * (M.face * swap a b)) * (swap a b * M.edge) =
    swap b (bypass M.vertex a b) * (swap a (M.vertex a) * M.vertex)
  rw [h.crossed_b,crossed_a,h.vertex_b,h.vertex_a]
  simp only [vertex,mul_assoc]
  rw [← mul_assoc (swap a b),swap_mul_self,one_mul]
end MergeSide

variable [DecidableEq D]

/-- Delete the paired sides and join the remaining oriented boundaries.
Unlike cancellation of an entire equal pair of cells, this works when the
remaining boundaries differ. -/
def mergeEdge (h : M.MergeSide a b) : PictureMap {x // OffPair a b x} where
  face := erasePair (M.face * swap a b) h.ne
  edge := M.edge.subtypePerm h.edge_invariant
  edge_sq := by ext x; exact M.edge_edge x.val
  edge_ne := by intro x he; exact M.edge_ne x.val (congrArg Subtype.val he)

lemma mergeEdge_vertex (h : M.MergeSide a b) :
    (M.mergeEdge h).vertex = erasePair M.vertex h.ne := by
  ext x
  change bypassPair (M.face * swap a b) a b (M.edge x.val) = bypassPair M.vertex a b x.val
  have hx := (h.edge_invariant x.val).mpr x.property
  have he := congrArg (fun p : Perm D => p x.val) h.erase_identity
  simpa only [mul_apply,swap_apply_of_ne_of_ne hx.1 hx.2] using he

variable [Fintype D]

lemma mergeEdge_faces (h : M.MergeSide a b) :
    cycles (M.mergeEdge h).face + 1 = cycles M.face := by
  have ha : (M.face * swap a b) a ≠ a := by rw [MergeSide.crossed_a]; exact h.face_right_ne_left
  have hb : bypass (M.face * swap a b) a b ≠ b := by rw [h.crossed_b]; exact h.face_left_ne_right
  change cycles (erasePair (M.face * swap a b) h.ne) + 1 = _
  rw [erasePair_cycles _ h.ne ha hb]
  exact cycles_merge_right M.face h.distinct_faces

lemma mergeEdge_vertices (h : M.MergeSide a b) :
    cycles (M.mergeEdge h).vertex = cycles M.vertex := by
  rw [mergeEdge_vertex]
  apply erasePair_cycles _ h.ne
  · rw [h.vertex_a]; exact h.face_right_ne_left
  · rw [h.vertex_b]; exact h.face_left_ne_right

lemma mergeEdge_euler (h : M.MergeSide a b) : (M.mergeEdge h).euler = M.euler := by
  have hf := M.mergeEdge_faces h
  have hv := M.mergeEdge_vertices h
  have hd := card_offPair h.ne
  have hde := M.card_darts_even
  have hde' := (M.mergeEdge h).card_darts_even
  rw [euler,euler,hv]
  obtain ⟨k,hk⟩ := hde
  obtain ⟨l,hl⟩ := hde'
  have hn : (Fintype.card {x // OffPair a b x} : ℤ) + 2 = Fintype.card D := by exact_mod_cast hd
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
