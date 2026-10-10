import Mathlib
import OAI.Geometry.HyperbolicGroups.PermEuler
import OAI.Geometry.HyperbolicGroups.PictureTriangulation
import OAI.Geometry.HyperbolicGroups.PictureUnderlyingGraph
import OAI.Geometry.HyperbolicGroups.PictureMapFurther

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

omit [DecidableEq D] in
lemma star_vertex_lift : SameCycle.setoid M.vertex ≤
    Setoid.comap Sum.inl (SameCycle.setoid M.triangulation.vertex) := by
  apply sameCycle_le_of_apply
  intro x
  have h : M.triangulation.vertex.SameCycle (.inl x)
      (M.triangulation.vertex (M.triangulation.vertex (.inl x))) :=
    SameCycle.rfl.apply_right.apply_right
  rw [M.triangulation_vertex_left,M.triangulation_vertex_middle] at h
  exact h

omit [DecidableEq D] [Fintype D] in
lemma star_center_lift {x y : D} (h : M.face.SameCycle x y) :
    M.triangulation.vertex.SameCycle (.inr (.inr x)) (.inr (.inr y)) :=
  semiconj_perm_sameCycle (f := M.face⁻¹) (t := M.triangulation.vertex)
    (j := fun x => Sum.inr (Sum.inr x)) (fun _ => rfl) h.inv

/-- The new vertices are exactly the old vertices plus the separate centers
of the old faces. This retains all original vertex identifications. -/
def starVertexClass : StarDart D → M.GraphVertex ⊕ Quotient (SameCycle.setoid M.face)
  | .inl x => .inl (M.vertexClass x)
  | .inr (.inl x) => .inl (M.vertexClass (M.face x))
  | .inr (.inr x) => .inr (Quotient.mk _ x)

omit [DecidableEq D] [Fintype D] in
lemma starVertexClass_step (z : StarDart D) :
    M.starVertexClass (M.triangulation.vertex z) = M.starVertexClass z := by
  rcases z with z | (z | z)
  · change Sum.inl (M.vertexClass (M.vertex z)) = Sum.inl (M.vertexClass z)
    exact congrArg Sum.inl (Quotient.sound SameCycle.rfl.apply_left)
  · rfl
  · change Sum.inr (Quotient.mk (SameCycle.setoid M.face) (M.face⁻¹ z)) =
      Sum.inr (Quotient.mk (SameCycle.setoid M.face) z)
    exact congrArg Sum.inr (Quotient.sound SameCycle.rfl.symm_apply_left)

omit [DecidableEq D] in
lemma star_vertex_cycle (x y : StarDart D) :
    M.triangulation.vertex.SameCycle x y ↔ M.starVertexClass x = M.starVertexClass y := by
  constructor
  · intro h
    exact sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm (M.GraphVertex ⊕ Quotient (SameCycle.setoid M.face))))
      (j := M.starVertexClass) M.starVertexClass_step h)
  · rcases x with x | (x | x) <;> rcases y with y | (y | y)
    · intro h; exact M.star_vertex_lift (Quotient.exact (Sum.inl.inj h))
    · intro h
      have hh := M.star_vertex_lift (Quotient.exact (Sum.inl.inj h))
      change M.triangulation.vertex.SameCycle (.inl x)
        (M.triangulation.vertex (.inr (.inl y))) at hh
      exact hh.of_apply_right
    · intro h; exact False.elim (Sum.inl_ne_inr h)
    · intro h
      have hh := M.star_vertex_lift (Quotient.exact (Sum.inl.inj h))
      change M.triangulation.vertex.SameCycle
        (M.triangulation.vertex (.inr (.inl x))) (.inl y) at hh
      exact hh.of_apply_left
    · intro h
      have hh := M.star_vertex_lift (Quotient.exact (Sum.inl.inj h))
      change M.triangulation.vertex.SameCycle
        (M.triangulation.vertex (.inr (.inl x)))
        (M.triangulation.vertex (.inr (.inl y))) at hh
      exact hh.of_apply_left.of_apply_right
    · intro h; exact False.elim (Sum.inl_ne_inr h)
    · intro h; exact False.elim (Sum.inr_ne_inl h)
    · intro h; exact False.elim (Sum.inr_ne_inl h)
    · intro h; exact M.star_center_lift (Quotient.exact (Sum.inr.inj h))

omit [DecidableEq D] [Fintype D] in
lemma starVertexClass_surjective : Function.Surjective M.starVertexClass := by
  intro z
  rcases z with z | z
  · obtain ⟨x,rfl⟩ := Quotient.exists_rep z
    exact ⟨.inl x,rfl⟩
  · obtain ⟨x,rfl⟩ := Quotient.exists_rep z
    exact ⟨.inr (.inr x),rfl⟩

lemma triangulation_vertex_cycles : cycles M.triangulation.vertex = cycles M.vertex + cycles M.face := by
  rw [cycles_eq_card_classes,
    card_quotient_of_classifier _ M.starVertexClass M.star_vertex_cycle M.starVertexClass_surjective,
    Nat.card_sum,Nat.cast_add,← cycles_eq_card_classes,← cycles_eq_card_classes]

omit [DecidableEq D] in
lemma star_components_lift : M.components ≤ Setoid.comap Sum.inl M.triangulation.components := by
  apply M.components_le
  · intro x
    apply M.triangulation.components.trans'
      (M.triangulation.face_le_components
        (show M.triangulation.face.SameCycle (.inl x) (.inr (.inl x)) from SameCycle.rfl.apply_right))
    exact M.triangulation.vertex_le_components
      (show M.triangulation.vertex.SameCycle (.inr (.inl x)) (.inl (M.face x)) from SameCycle.rfl.apply_right)
  · intro x
    exact M.triangulation.edge_le_components
      (show M.triangulation.edge.SameCycle (.inl x) (.inl (M.edge x)) from SameCycle.rfl.apply_right)

def starComponent (x : StarDart D) : Quotient M.components :=
  Quotient.mk M.components (starIndex x)

omit [DecidableEq D] in
lemma star_components (x y : StarDart D) :
    M.triangulation.components x y ↔ M.starComponent x = M.starComponent y := by
  have hle : M.triangulation.components ≤ Setoid.ker M.starComponent := by
    apply M.triangulation.components_le
    · rintro (z | (z | z)) <;> rfl
    · rintro (z | (z | z))
      · exact Quotient.sound (M.edge_le_components SameCycle.rfl.apply_right)
      · exact Quotient.sound (M.face_le_components SameCycle.rfl.apply_right)
      · exact Quotient.sound (M.face_le_components SameCycle.rfl.symm_apply_right)
  refine ⟨fun h => hle h,?_⟩
  intro h
  exact M.triangulation.components.trans'
    (M.triangulation.face_le_components (M.star_face_to_left x))
    (M.triangulation.components.trans'
      (M.star_components_lift (Quotient.exact h))
      (M.triangulation.face_le_components (M.star_face_to_left y).symm))

omit [DecidableEq D] in
lemma triangulation_components_card : Nat.card (Quotient M.triangulation.components) =
    Nat.card (Quotient M.components) := by
  apply card_quotient_of_classifier _ M.starComponent M.star_components
  intro z
  obtain ⟨x,rfl⟩ := Quotient.exists_rep z
  exact ⟨.inl x,rfl⟩

lemma triangulation_euler : M.triangulation.euler = M.euler := by
  obtain ⟨k,hk⟩ := M.card_darts_even
  rw [euler,euler,M.triangulation_vertex_cycles,M.triangulation_face_cycles]
  change cycles M.vertex + cycles M.face + (Fintype.card D : ℤ) -
    (Fintype.card (D ⊕ (D ⊕ D)) : ℤ) / 2 = _
  rw [Fintype.card_sum,Fintype.card_sum,Nat.cast_add,Nat.cast_add]
  omega

/-- Literal face starring preserves genus zero and connected-component count;
its dual is therefore a genuine degree-three genus-zero ribbon graph. -/
theorem triangulation_genusZero (h : M.GenusZero) : M.triangulation.GenusZero := by
  change M.triangulation.euler = 2*(Nat.card (Quotient M.triangulation.components) : ℤ)
  rw [M.triangulation_euler,M.triangulation_components_card]
  exact h

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
