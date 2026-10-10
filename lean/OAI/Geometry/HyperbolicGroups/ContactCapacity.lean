import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureContact

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
attribute [local instance] Classical.propDecidable
variable {X Y : Type*} [Fintype X] (P : PictureMap X)
variable (selected raw : X → Prop) (hraw : ∀ x, raw (P.edge x) ↔ raw x)
variable (position : X → Y) (p : Y)

abbrev IncidentContact := {e : P.Contact selected raw // position e.val = p ∨ position (P.edge e.val) = p}
abbrev PositionSide := {x : SelectedSide selected raw // position x.val = p}

def contactEnd (e : P.IncidentContact selected raw position p) :
    P.Contact selected raw ⊕ P.Contact selected raw :=
  if position e.val.val = p then .inl e.val else .inr e.val

lemma contactEnd_position (e : P.IncidentContact selected raw position p) :
    position (P.contactSide selected raw hraw (P.contactEnd selected raw position p e)).val = p := by
  unfold contactEnd
  split_ifs with h
  · exact h
  · exact e.property.resolve_left h

lemma contactEnd_injective : Function.Injective (P.contactEnd selected raw position p) := by
  intro e f h
  have hh := congrArg (Sum.elim id id) h
  simp only [contactEnd,apply_ite,Sum.elim_inl,Sum.elim_inr,id_eq,ite_self] at hh
  exact Subtype.ext hh

include hraw in
/-- Contacts charge actual side copies injectively, even if the contact graph
has cycles or parallel edges. This is not a forest assumption. -/
theorem contact_capacity : Fintype.card (P.IncidentContact selected raw position p) ≤
    Fintype.card (PositionSide selected raw position p) := by
  let g : P.IncidentContact selected raw position p → PositionSide selected raw position p := fun e =>
    ⟨⟨(P.contactSide selected raw hraw (P.contactEnd selected raw position p e)).val,
      (P.contactSide selected raw hraw (P.contactEnd selected raw position p e)).property.1,
      (P.contactSide selected raw hraw (P.contactEnd selected raw position p e)).property.2.1⟩,
      P.contactEnd_position selected raw hraw position p e⟩
  apply Fintype.card_le_of_injective g
  intro e f h
  apply P.contactEnd_injective selected raw position p
  apply P.contactSide_injective selected raw hraw
  apply Subtype.ext
  exact congrArg (fun x : PositionSide selected raw position p => x.val.val) h

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

section

end
end

end OAI
