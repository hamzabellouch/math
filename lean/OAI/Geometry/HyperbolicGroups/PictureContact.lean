import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {X : Type*} [Fintype X] (P : PictureMap X)
variable (selected raw : X → Prop) (hraw : ∀ x, raw (P.edge x) ↔ raw x)

abbrev SelectedSide := {x : X // raw x ∧ selected x}
abbrev InternalSide := {x : X // raw x ∧ selected x ∧ selected (P.edge x)}
abbrev BoundarySide := {x : X // raw x ∧ selected x ∧ ¬selected (P.edge x)}
def number (_P : PictureMap X) (x : X) : Fin (Fintype.card X) := Fintype.equivFin X x
abbrev Contact := {x : X // raw x ∧ selected x ∧ selected (P.edge x) ∧
  P.number x < P.number (P.edge x)}

lemma number_ne (x : X) : P.number x ≠ P.number (P.edge x) := by
  intro h
  exact P.edge_ne x ((Fintype.equivFin X).injective h).symm

def contactSide : P.Contact selected raw ⊕ P.Contact selected raw → P.InternalSide selected raw
  | .inl x => ⟨x.val,x.property.1,x.property.2.1,x.property.2.2.1⟩
  | .inr x => ⟨P.edge x.val,(hraw x.val).mpr x.property.1,x.property.2.2.1,by
      rw [P.edge_edge]; exact x.property.2.1⟩

lemma contactSide_injective : Function.Injective (P.contactSide selected raw hraw) := by
  intro x y he
  have hv := congrArg Subtype.val he
  rcases x with x | x <;> rcases y with y | y <;> dsimp only [contactSide] at hv
  · exact congrArg Sum.inl (Subtype.ext hv)
  · change x.val = P.edge y.val at hv
    have h1 := x.property.2.2.2
    rw [hv,P.edge_edge] at h1
    exact False.elim (not_lt_of_ge (le_of_lt y.property.2.2.2) h1)
  · change P.edge x.val = y.val at hv
    have h1 := y.property.2.2.2
    rw [← hv,P.edge_edge] at h1
    exact False.elim (not_lt_of_ge (le_of_lt x.property.2.2.2) h1)
  · exact congrArg Sum.inr (Subtype.ext (P.edge.injective hv))

lemma contactSide_surjective : Function.Surjective (P.contactSide selected raw hraw) := by
  intro y
  by_cases hh : P.number y.val < P.number (P.edge y.val)
  · exact ⟨.inl ⟨y.val,y.property.1,y.property.2.1,y.property.2.2,hh⟩,rfl⟩
  · have hg : P.number (P.edge y.val) < P.number y.val :=
      lt_of_le_of_ne (le_of_not_gt hh) (P.number_ne y.val).symm
    refine ⟨.inr ⟨P.edge y.val,(hraw y.val).mpr y.property.1,y.property.2.2,?_,?_⟩,?_⟩
    · rw [P.edge_edge]; exact y.property.2.1
    · rw [P.edge_edge]; exact hg
    · apply Subtype.ext; exact P.edge_edge y.val

include hraw in
lemma internal_card : Fintype.card (P.InternalSide selected raw) =
    2 * Fintype.card (P.Contact selected raw) := by
  have h := Fintype.card_congr (Equiv.ofBijective _
    ⟨P.contactSide_injective selected raw hraw,P.contactSide_surjective selected raw hraw⟩)
  simpa only [Fintype.card_sum,two_mul] using h.symm

def boundaryInternalSide : P.BoundarySide selected raw ⊕ P.InternalSide selected raw →
    SelectedSide selected raw
  | .inl x => ⟨x.val,x.property.1,x.property.2.1⟩
  | .inr x => ⟨x.val,x.property.1,x.property.2.1⟩

omit [Fintype X] in
lemma boundaryInternalSide_bijective : Function.Bijective (P.boundaryInternalSide selected raw) := by
  constructor
  · intro x y he
    have hv := congrArg Subtype.val he
    rcases x with x | x <;> rcases y with y | y <;> dsimp only [boundaryInternalSide] at hv
    · exact congrArg Sum.inl (Subtype.ext hv)
    · exact False.elim (x.property.2.2 (by rw [hv]; exact y.property.2.2))
    · exact False.elim (y.property.2.2 (by rw [← hv]; exact x.property.2.2))
    · exact congrArg Sum.inr (Subtype.ext hv)
  · intro x
    by_cases h : selected (P.edge x.val)
    · exact ⟨.inr ⟨x.val,x.property.1,x.property.2,h⟩,rfl⟩
    · exact ⟨.inl ⟨x.val,x.property.1,x.property.2,h⟩,rfl⟩

include hraw in
/-- Exact side counting for an arbitrary selection of faces: each kept
internal pairing uses two selected sides, each boundary side one. -/
theorem boundary_contacts_eq : Fintype.card (P.BoundarySide selected raw) +
    2 * Fintype.card (P.Contact selected raw) = Fintype.card (SelectedSide selected raw) := by
  rw [← P.internal_card selected raw hraw,← Fintype.card_sum]
  exact Fintype.card_congr (Equiv.ofBijective _ (P.boundaryInternalSide_bijective selected raw))

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

section

end
end

end OAI
