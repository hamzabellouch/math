import Mathlib

namespace OAI

namespace PiExponent.AddEquivSignedSum
open scoped BigOperators

theorem map_signed_sum {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (E : A ≃+ B) (q : ℕ) (f : Fin (q+2) → A) :
    E (∑ k, (-1 : ℤ)^k.val • f k) = ∑ k, (-1 : ℤ)^k.val • E (f k) := by
  simp only [map_sum, map_zsmul]

theorem map_signed_sum_eq {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (E : A ≃+ B) (q : ℕ) (f : Fin (q+2) → A) (g : Fin (q+2) → B)
    (h : ∀ k, E (f k) = g k) :
    E (∑ k, (-1 : ℤ)^k.val • f k) = ∑ k, (-1 : ℤ)^k.val • g k := by
  rw [map_signed_sum]
  exact Finset.sum_congr rfl (fun k _ => congrArg (fun z => (-1 : ℤ)^k.val • z) (h k))

end PiExponent.AddEquivSignedSum

end OAI
