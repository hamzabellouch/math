import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureGenus
import OAI.Geometry.HyperbolicGroups.PolygonSphere
import OAI.Geometry.HyperbolicGroups.EdgeMerge

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
namespace PictureMap
variable {M : PictureMap D} {a b : D} (h : M.MergeSide a b)
namespace MergeSide
include h

lemma old_face_le_crossed : SameCycle.setoid M.face ≤ SameCycle.setoid (M.face * swap a b) := by
  have hab : (M.face * swap a b).SameCycle a b := sameCycle_after_swap_right M.face h.distinct_faces
  apply sameCycle_le_of_apply
  intro x
  have ht := sameCycle_swap_le (s := SameCycle.setoid (M.face * swap a b)) hab (SameCycle.rfl (x := x)).apply_right
  have hf := (SameCycle.rfl (f := M.face * swap a b) (x := swap a b x)).apply_right
  have he : (M.face * swap a b) (swap a b x) = M.face x := by simp
  rw [he] at hf
  exact ht.trans hf

lemma crossed_le_components : SameCycle.setoid (M.face * swap a b) ≤ M.components := by
  apply sameCycle_mul_le M.face_le_components
  apply sameCycle_swap_le
  rw [← h.paired]
  exact M.edge_le_components SameCycle.rfl.apply_right

def representative (x : D) : {x // OffPair a b x} :=
  if hx : OffPair a b x then ⟨x,hx⟩ else
    ⟨M.face a,h.left_nonmonogon,h.face_left_ne_right⟩

omit [DecidableEq D] [Fintype D] in
lemma representative_kept (x : {x // OffPair a b x}) : h.representative x.val = x := by
  simp only [representative,dite_eq_left x.property]
omit [DecidableEq D] [Fintype D] in
lemma representative_a : h.representative a = ⟨M.face a,h.left_nonmonogon,h.face_left_ne_right⟩ := by
  simp [representative,OffPair]
omit [DecidableEq D] [Fintype D] in
lemma representative_b : h.representative b = ⟨M.face a,h.left_nonmonogon,h.face_left_ne_right⟩ := by
  simp [representative,OffPair]

lemma representative_crossed (x : D) :
    (M.face * swap a b).SameCycle x (h.representative x).val := by
  by_cases hx : OffPair a b x
  · simp only [representative,dite_eq_left hx]; exact SameCycle.rfl
  · have hh : x = a ∨ x = b := by unfold OffPair at hx; tauto
    rcases hh with rfl|rfl
    · rw [h.representative_a]
      exact h.old_face_le_crossed SameCycle.rfl.apply_right
    · rw [h.representative_b]
      exact (sameCycle_after_swap_right M.face h.distinct_faces).symm.trans
        (h.old_face_le_crossed SameCycle.rfl.apply_right)

lemma representative_face (x : D) :
    (M.mergeEdge h).face.SameCycle (h.representative x) (h.representative (M.face x)) := by
  change (erasePair (M.face * swap a b) h.ne).SameCycle _ _
  rw [erasePair_orbits]
  exact (h.representative_crossed x).symm.trans
    ((h.old_face_le_crossed SameCycle.rfl.apply_right).trans (h.representative_crossed (M.face x)))

omit [Fintype D] in
lemma representative_edge (x : D) :
    (M.mergeEdge h).components (h.representative x) (h.representative (M.edge x)) := by
  by_cases hx : OffPair a b x
  · have he := (h.edge_invariant x).mpr hx
    have hr : h.representative (M.edge x) = (M.mergeEdge h).edge (h.representative x) := by
      apply Subtype.ext
      simp only [representative,dite_eq_left hx,dite_eq_left he,mergeEdge,subtypePerm_apply]
    rw [hr]
    exact (M.mergeEdge h).edge_le_components SameCycle.rfl.apply_right
  · have hh : x = a ∨ x = b := by unfold OffPair at hx; tauto
    rcases hh with rfl|rfl
    · rw [h.paired,h.representative_a,h.representative_b]
      try exact (M.mergeEdge h).components.refl' _
    · rw [h.paired_back,h.representative_a,h.representative_b]
      try exact (M.mergeEdge h).components.refl' _

lemma retained_components :
    (M.mergeEdge h).components ≤ M.components.comap (Subtype.val : {x // OffPair a b x} → D) := by
  apply (M.mergeEdge h).components_le
  · intro x
    apply h.crossed_le_components
    apply (erasePair_orbits (M.face * swap a b) h.ne x ((M.mergeEdge h).face x)).mp
    exact SameCycle.rfl.apply_right
  · intro x
    exact M.edge_le_components (SameCycle.rfl (x := x.val)).apply_right

/-- No component is created or lost by deleting a common side of distinct
faces, even when their boundaries also touch elsewhere. -/
theorem component_card : Nat.card (Quotient (M.mergeEdge h).components) = Nat.card (Quotient M.components) := by
  let N := M.mergeEdge h
  let j : D → Quotient N.components := fun x => Quotient.mk _ (h.representative x)
  have hforward : M.components ≤ Setoid.ker j := by
    apply M.components_le
    · intro x
      exact Quotient.sound (N.face_le_components (h.representative_face x))
    · intro x
      exact Quotient.sound (h.representative_edge x)
  have hrel (x y : D) : M.components x y ↔ j x = j y := by
    constructor
    · intro hh; exact hforward hh
    · intro he
      have hn : N.components (h.representative x) (h.representative y) := Quotient.exact he
      have hh := h.retained_components hn
      exact M.components.trans' (h.crossed_le_components (h.representative_crossed x))
        (M.components.trans' hh (M.components.symm' (h.crossed_le_components (h.representative_crossed y))))
  have hj : Function.Surjective j := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      refine ⟨x.val,?_⟩
      change Quotient.mk N.components (h.representative x.val) = Quotient.mk N.components x
      rw [h.representative_kept]
  exact (card_quotient_of_classifier M.components j hrel hj).symm
end MergeSide

/-- The connected edge-cancellation surgery preserves literal genus zero
and removes exactly one face and two darts. -/
theorem mergeEdge_genusZero (hG : M.GenusZero) : (M.mergeEdge h).GenusZero := by
  change (M.mergeEdge h).euler = _
  rw [M.mergeEdge_euler h,h.component_card]
  exact hG

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
