import Mathlib
import OAI.Geometry.HyperbolicGroups.ColoredApex
import OAI.Geometry.HyperbolicGroups.SetoidRestrict

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

omit [DecidableEq D] in
lemma invariant_of_sameCycle {P : D → Prop} (p : Perm D)
    (hp : ∀ x, P (p x) ↔ P x) {a b : D} (hab : p.SameCycle a b) : P a ↔ P b := by
  have hh : SameCycle.setoid p ≤ Setoid.ker P :=
    sameCycle_le_of_apply (fun x => propext (hp x).symm)
  exact Iff.of_eq (hh hab)

lemma cycles_subtype_split {P : D → Prop} (p : Perm D)
    (hp : ∀ x, P (p x) ↔ P x) :
    cycles p = cycles (p.subtypePerm hp) +
      cycles (p.subtypePerm (p := fun x => ¬ P x) (fun x => not_congr (hp x))) := by
  have hc := card_quotient_split (SameCycle.setoid p) P (invariant_of_sameCycle p hp)
  have he (Q : D → Prop) (hQ : ∀ x, Q (p x) ↔ Q x) :
      Nat.card (Quotient ((SameCycle.setoid p).comap (Subtype.val : Subtype Q → D))) =
        Nat.card (Quotient (SameCycle.setoid (p.subtypePerm hQ))) := by
    exact Nat.card_congr (Quotient.congrRight (fun a b => (sameCycle_subtypePerm_iff p hQ a b).symm))
  rw [he P hp,he (fun x => ¬ P x) (fun x => not_congr (hp x))] at hc
  simp only [cycles_eq_card_classes]
  exact_mod_cast hc


end HyperbolicObstruction.PictureSwitch
end
end
end

end OAI
