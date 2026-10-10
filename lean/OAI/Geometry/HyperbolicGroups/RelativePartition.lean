import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureContact

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {X I : Type*} [Fintype X] [DecidableEq X] [Fintype I]
variable (P : PictureMap X) (active : X → Prop) (part : X → I)

/-- One side of a selected INTERIOR fragment. The complement includes the
protected outside, even when its arbitrary partition label agrees. -/
abbrev RelativePartBoundary (i : I) :=
  {x : X // active x ∧ part x = i ∧ ¬ (active (P.edge x) ∧ part (P.edge x) = i)}
instance (i : I) : Fintype (RelativePartBoundary P active part i) := Fintype.ofFinite _

abbrev OutsideContact := {x : X // active x ∧ ¬ active (P.edge x)}
instance : Fintype (OutsideContact P active) := Fintype.ofFinite _

abbrev RelativeCutContact := {x : X // active x ∧ active (P.edge x) ∧
  part x ≠ part (P.edge x) ∧ P.number x < P.number (P.edge x)}
instance : Fintype (RelativeCutContact P active part) := Fintype.ofFinite _

omit [DecidableEq X] in
/-- Exact relative boundary accounting, retaining loops and parallel contacts:
outside contacts occur once, contacts cut between interior parts twice. -/
theorem sum_relative_part_boundary :
    (∑ i, Fintype.card (RelativePartBoundary P active part i)) =
      Fintype.card (OutsideContact P active) +
        2 * Fintype.card (RelativeCutContact P active part) := by
  let raw : X → Prop := fun x => ¬ active x ∨ ¬ active (P.edge x) ∨ part x ≠ part (P.edge x)
  have hr : ∀ x, raw (P.edge x) ↔ raw x := by
    intro x
    dsimp only [raw]
    rw [P.edge_edge]
    tauto
  have h := P.boundary_contacts_eq active raw hr
  have hS : (∑ i, Fintype.card (RelativePartBoundary P active part i)) =
      Fintype.card (PictureMap.SelectedSide active raw) := by
    rw [← Fintype.card_sigma]
    apply Fintype.card_congr
    exact {
      toFun := fun p => ⟨p.2.val,by
        have hx := p.2.property
        dsimp only [raw]
        refine ⟨Or.inr ?_,hx.1⟩
        by_cases he : active (P.edge p.2.val)
        · right
          intro hp
          exact hx.2.2 ⟨he,hp.symm.trans hx.2.1⟩
        · exact Or.inl he⟩
      invFun := fun x => ⟨part x.val,x.val,x.property.2,rfl,by
        have hx := x.property
        dsimp only [raw] at hx
        tauto⟩
      left_inv := by rintro ⟨i,x,hx,hi,he⟩; cases hi; rfl
      right_inv := fun _ => rfl }
  have hB : Fintype.card (P.BoundarySide active raw) =
      Fintype.card (OutsideContact P active) := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    dsimp only [raw]
    tauto
  have hC : Fintype.card (P.Contact active raw) =
      Fintype.card (RelativeCutContact P active part) := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    dsimp only [raw]
    tauto
  simp only [← Nat.card_eq_fintype_card] at hS hB hC h ⊢
  rw [hS,← hB,← hC]
  exact h.symm

/-- Contacts from the interior to an enumerated outside are bounded by its
literal length. Outside-to-outside free boundary folds are NOT counted. -/
theorem outside_contacts_le_length (xs : List X)
    (ha : ∀ x, active x ↔ x ∉ xs) :
    Fintype.card (OutsideContact P active) ≤ xs.length := by
  let j : OutsideContact P active → {x : X // x ∈ xs} := fun x =>
    ⟨P.edge x.val,by
      have hh := x.property.2
      rw [ha] at hh
      exact Classical.not_not.mp hh⟩
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    exact P.edge.injective (congrArg Subtype.val he)
  have hh := Fintype.card_le_of_injective j hj
  have hc : Fintype.card {x : X // x ∈ xs} = xs.toFinset.card :=
    Fintype.card_of_subtype xs.toFinset (by intro x; exact List.mem_toFinset)
  rw [hc] at hh
  exact hh.trans (List.toFinset_card_le xs)

/-- Source03's summation bound on a disk, before any separator existence or
small-fragment estimate is used. This is a literal finite-side identity. -/
theorem sum_relative_boundary_le (xs : List X)
    (ha : ∀ x, active x ↔ x ∉ xs) :
    (∑ i, Fintype.card (RelativePartBoundary P active part i)) ≤
      xs.length + 2 * Fintype.card (RelativeCutContact P active part) := by
  rw [sum_relative_part_boundary]
  exact Nat.add_le_add_right (outside_contacts_le_length P active xs ha) _

end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
