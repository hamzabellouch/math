import Mathlib.Algebra.Order.BigOperators.Group.Finset
import OAI.NumberTheory.Ostmann.Characters.AnchorPairCode
import OAI.NumberTheory.Ostmann.Tree.PartitionMatching

namespace OAI

/-! # The number of code-preserving bulk matchings -/

namespace Ostmann

open scoped BigOperators Classical

theorem card_anchor_slot_fiber_le {n m : ℕ} (α : Fin n → ℤ)
    (hα : ∀ j, α j = 1 ∨ α j = -1) (code : Fin n → ℤ × ℤ) :
    Fintype.card {x : (Fin n → Bool) × Fin m // finiteAnchorCode α x.1 = code} ≤ 2 * m := by
  calc
    _ = Fintype.card ({t : Fin n → Bool // finiteAnchorCode α t = code} × Fin m) :=
      Fintype.card_congr (slotFiberEquiv (finiteAnchorCode α) m code)
    _ = Fintype.card {t : Fin n → Bool // finiteAnchorCode α t = code} * m := by
      rw [Fintype.card_prod, Fintype.card_fin]
    _ ≤ _ := Nat.mul_le_mul_right m (card_anchorCode_fiber_le_two α hα code)

/-- Each of the `2^n * m` labeled bulk slots has at most `2*m` possible
counterparts. Injectivity of the matching can only reduce the count. -/
theorem card_anchor_matching_le {n m : ℕ} (α : Fin n → ℤ)
    (hα : ∀ j, α j = 1 ∨ α j = -1) :
    Fintype.card (PartitionMatching
      (fun x : (Fin n → Bool) × Fin m => finiteAnchorCode α x.1)
      (fun x : (Fin n → Bool) × Fin m => finiteAnchorCode α x.1)) ≤
      (2 * m) ^ (2 ^ n * m) := by
  let D := (Fin n → Bool) × Fin m
  let code : D → (Fin n → ℤ × ℤ) := fun x => finiteAnchorCode α x.1
  let f : PartitionMatching code code → ∀ x : D, {y : D // code y = code x} :=
    fun e x => ⟨e.val x, e.property x⟩
  have hf : Function.Injective f := by
    intro e e' he
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact congrArg Subtype.val (congrFun he x)
  calc
    _ ≤ Fintype.card (∀ x : D, {y : D // code y = code x}) :=
      Fintype.card_le_of_injective f hf
    _ = ∏ x : D, Fintype.card {y : D // code y = code x} := Fintype.card_pi
    _ ≤ ∏ _x : D, 2 * m := Finset.prod_le_prod fun x _ =>
      card_anchor_slot_fiber_le α hα (code x)
    _ = _ := by simp [D]

end Ostmann

end OAI
