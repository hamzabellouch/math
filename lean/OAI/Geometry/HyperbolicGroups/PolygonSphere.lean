import Mathlib
import OAI.Geometry.HyperbolicGroups.CycleCount

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable

variable {D B : Type*}

lemma card_quotient_of_classifier (s : Setoid D) (j : D → B)
    (h : ∀ x y, s x y ↔ j x = j y) (hs : Function.Surjective j) :
    Nat.card (Quotient s) = Nat.card B := by
  have he : s = Setoid.ker j := by ext x y; exact h x y
  rw [he]
  exact Nat.card_congr (Setoid.quotientKerEquivOfSurjective j hs)

lemma cycles_of_classifier [DecidableEq D] [Fintype D] [Fintype B]
    (f : Perm D) (j : D → B) (h : ∀ x y, f.SameCycle x y ↔ j x = j y)
    (hs : Function.Surjective j) : cycles f = Fintype.card B := by
  rw [cycles_eq_card_classes,card_quotient_of_classifier (SameCycle.setoid f) j h hs,Nat.card_eq_fintype_card]


end HyperbolicObstruction.PictureSwitch
end
end
end

end OAI
