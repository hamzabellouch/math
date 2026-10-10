import Mathlib
import OAI.Geometry.HyperbolicGroups.IndexedFace
import OAI.Geometry.HyperbolicGroups.PolygonSphere

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*}
namespace PictureMap
variable (M : PictureMap D)

/-- Three individually indexed sides for each old side: its old edge, and
two radii to the new center of the old face. This is literal face starring. -/
abbrev StarDart (D : Type*) := D ⊕ (D ⊕ D)

def starFace : Perm (StarDart D) where
  toFun := fun x => match x with
    | .inl x => .inr (.inl x)
    | .inr (.inl x) => .inr (.inr x)
    | .inr (.inr x) => .inl x
  invFun := fun x => match x with
    | .inl x => .inr (.inr x)
    | .inr (.inl x) => .inl x
    | .inr (.inr x) => .inr (.inl x)
  left_inv := by rintro (x | (x | x)) <;> rfl
  right_inv := by rintro (x | (x | x)) <;> rfl

def starEdgeFun : StarDart D → StarDart D
  | .inl x => .inl (M.edge x)
  | .inr (.inl x) => .inr (.inr (M.face x))
  | .inr (.inr x) => .inr (.inl (M.face⁻¹ x))

lemma starEdge_sq (x : StarDart D) : M.starEdgeFun (M.starEdgeFun x) = x := by
  rcases x with x | (x | x) <;> simp only [starEdgeFun,M.edge_edge,Perm.inv_def,
    Equiv.symm_apply_apply,Equiv.apply_symm_apply]

def starEdge : Perm (StarDart D) where
  toFun := M.starEdgeFun
  invFun := M.starEdgeFun
  left_inv := M.starEdge_sq
  right_inv := M.starEdge_sq

/-- A triangular rotation system obtained by starring every face; old edge
copies are preserved, and each old face has a distinct new center. -/
def triangulation : PictureMap (StarDart D) where
  face := starFace
  edge := M.starEdge
  edge_sq := by ext x; exact M.starEdge_sq x
  edge_ne := by
    rintro (x | (x | x)) h
    · exact M.edge_ne x (Sum.inl.inj h)
    · exact Sum.inr_ne_inl (Sum.inr.inj h)
    · exact Sum.inl_ne_inr (Sum.inr.inj h)

@[simp] lemma triangulation_face_left (x : D) :
    M.triangulation.face (.inl x) = .inr (.inl x) := rfl
@[simp] lemma triangulation_face_middle (x : D) :
    M.triangulation.face (.inr (.inl x)) = .inr (.inr x) := rfl
@[simp] lemma triangulation_face_right (x : D) :
    M.triangulation.face (.inr (.inr x)) = .inl x := rfl
@[simp] lemma triangulation_vertex_left (x : D) :
    M.triangulation.vertex (.inl x) = .inr (.inl (M.edge x)) := rfl
@[simp] lemma triangulation_vertex_middle (x : D) :
    M.triangulation.vertex (.inr (.inl x)) = .inl (M.face x) := rfl
@[simp] lemma triangulation_vertex_right (x : D) :
    M.triangulation.vertex (.inr (.inr x)) = .inr (.inr (M.face⁻¹ x)) := rfl

def starIndex : StarDart D → D := Sum.elim id (Sum.elim id id)

lemma star_face_to_left (x : StarDart D) :
    M.triangulation.face.SameCycle x (.inl (starIndex x)) := by
  rcases x with x | (x | x)
  · exact SameCycle.rfl
  · exact (SameCycle.rfl (x := Sum.inl x)).apply_left
  · exact (SameCycle.rfl (x := Sum.inr (Sum.inr x))).apply_right

lemma triangulation_face_cycle (x y : StarDart D) :
    M.triangulation.face.SameCycle x y ↔ starIndex x = starIndex y := by
  constructor
  · intro h
    apply sameCycle_one.mp (semiconj_perm_sameCycle
      (t := (1 : Perm D)) (j := starIndex) ?_ h)
    rintro (z | (z | z)) <;> rfl
  · intro h
    exact (M.star_face_to_left x).trans (by rw [h]; exact (M.star_face_to_left y).symm)

variable [DecidableEq D] [Fintype D]

lemma triangulation_face_cycles : cycles M.triangulation.face = (Fintype.card D : ℤ) := by
  rw [cycles_eq_card_classes,card_quotient_of_classifier _ starIndex M.triangulation_face_cycle ?_]
  · rw [Nat.card_eq_fintype_card]
  · intro x; exact ⟨.inl x,rfl⟩

/-- All new faces have exactly three sides, including when the old map had
loops, multiple edges, or monogons. -/
lemma triangulation_face_degree (x : StarDart D) :
    Fintype.card {y : StarDart D // M.triangulation.face.SameCycle x y} = 3 := by
  rw [Fintype.card_of_subtype
    ({.inl (starIndex x),.inr (.inl (starIndex x)),.inr (.inr (starIndex x))} : Finset (StarDart D))
    (by
      rintro (y | (y | y)) <;> rw [M.triangulation_face_cycle] <;>
        simp [starIndex,eq_comm])]
  simp

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
