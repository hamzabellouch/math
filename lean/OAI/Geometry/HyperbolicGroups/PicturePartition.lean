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
universe u v w z k t r
variable {X I F : Type*} [Fintype X] [Fintype I] [Fintype F]

/-- Oriented side copies cut by a partition. Parallel contacts and self-contacts
remain literal side copies; no underlying-simple-graph collapse is made. -/
abbrev CutSide (P : PictureMap X) (part : X → I) := {x : X // part x ≠ part (P.edge x)}
instance (P : PictureMap X) (part : X → I) : Fintype (CutSide P part) := Fintype.ofFinite _
abbrev CutContact (P : PictureMap X) (part : X → I) :=
  {x : X // part x ≠ part (P.edge x) ∧ P.number x < P.number (P.edge x)}
instance (P : PictureMap X) (part : X → I) : Fintype (CutContact P part) := Fintype.ofFinite _

abbrev PartBoundary (P : PictureMap X) (part : X → I) (i : I) :=
  {x : X // part x = i ∧ part (P.edge x) ≠ i}
instance (P : PictureMap X) (part : X → I) (i : I) : Fintype (PartBoundary P part i) := Fintype.ofFinite _

lemma sum_part_boundary (P : PictureMap X) (part : X → I) :
    (∑ i, Fintype.card (PartBoundary P part i)) = Fintype.card (CutSide P part) := by
  rw [← Fintype.card_sigma]
  apply Fintype.card_congr
  exact {
    toFun := fun p => ⟨p.2.val,fun h => p.2.property.2 (h.symm.trans p.2.property.1)⟩
    invFun := fun x => ⟨part x.val,x.val,rfl,Ne.symm x.property⟩
    left_inv := by rintro ⟨i,x,hx,he⟩; cases hx; rfl
    right_inv := fun _ => rfl }

omit [Fintype I] in
lemma cut_sides_twice (P : PictureMap X) (part : X → I) :
    Fintype.card (CutSide P part) = 2 * Fintype.card (CutContact P part) := by
  let raw := fun x => part x ≠ part (P.edge x)
  have hr : ∀ x, raw (P.edge x) ↔ raw x := by intro x; dsimp only [raw]; rw [P.edge_edge]; exact ne_comm
  have hh := P.boundary_contacts_eq (fun _ => True) raw hr
  have : IsEmpty (P.BoundarySide (fun _ => True) raw) := ⟨fun x => x.property.2.2 trivial⟩
  simp only [Fintype.card_of_isEmpty,Nat.zero_add] at hh
  have h1 : Fintype.card (PictureMap.SelectedSide (fun _ => True) raw) = Fintype.card (CutSide P part) := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun _ => by simp only [and_true,raw])
  have h2 : Fintype.card (P.Contact (fun _ => True) raw) = Fintype.card (CutContact P part) := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun _ => by dsimp only [raw]; simp only [true_and])
  simp only [← Nat.card_eq_fintype_card] at h1 h2 hh ⊢
  rw [h1,h2] at hh
  omega

lemma sum_part_sizes (part : F → I) :
    (∑ i, Fintype.card {x : F // part x = i}) = Fintype.card F := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv part)

end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
