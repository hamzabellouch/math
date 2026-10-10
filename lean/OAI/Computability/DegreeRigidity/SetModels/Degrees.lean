import OAI.Computability.DegreeRigidity.Model
import Mathlib.Computability.TuringDegree
import Mathlib.Order.Hom.Basic

namespace OAI

namespace TuringRigidity

theorem reduces_refl (A : Oracle) : Reduces A A := TuringReducible.refl _
theorem reduces_trans {A B C : Oracle} (h : Reduces A B) (k : Reduces B C) :
    Reduces A C := TuringReducible.trans h k

def degree (A : Oracle) : Degree := toAntisymmetrization Reduces A

@[simp] theorem degree_le_iff (A B : Oracle) : degree A ≤ degree B ↔ Reduces A B := Iff.rfl

theorem degree_eq_iff (A B : Oracle) :
    degree A = degree B ↔ Reduces A B ∧ Reduces B A := by
  exact Quotient.eq

theorem degree_surjective : Function.Surjective degree := by
  intro a
  exact ⟨ofAntisymmetrization Reduces a, toAntisymmetrization_ofAntisymmetrization _ a⟩

theorem order_rigidity_of_inverse_le {α : Type*} [PartialOrder α]
    (h : ∀ π : α ≃o α, ∀ a, π.symm a ≤ a) :
    ∀ π : α ≃o α, ∀ a, π a = a := by
  intro π a
  apply le_antisymm
  · simpa using h π.symm a
  · simpa using π.monotone (h π a)

end TuringRigidity

end OAI
