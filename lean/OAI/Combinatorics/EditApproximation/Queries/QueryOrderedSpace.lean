import OAI.Combinatorics.EditApproximation.Queries.QueryCoordinateSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation



theorem queryEraseLoopAllocation_le_work {α : Type*} (equal : α → α → Bool × ℕ)
    (allocation : α → α → ℕ) (xs seen : List α) (h : ∀ a b, allocation a b ≤ (equal a b).2) :
    queryEraseLoopAllocation equal allocation xs seen ≤ (queryEraseLoopWithWork equal xs seen).2 := by
  induction xs generalizing seen with
  | nil => exact Nat.le_succ _
  | cons a xs ih =>
    have hm := memberByAllocation_le_work equal allocation a seen (fun b _ => h a b)
    have ht := ih (if (memberByWithWork equal a seen).1 then seen else a :: seen)
    unfold queryEraseLoopAllocation queryEraseLoopWithWork
    dsimp only
    exact Nat.add_le_add (Nat.add_le_add hm ht) (by split <;> decide)



theorem queryEraseAllocation_le_work {α : Type*} (equal : α → α → Bool × ℕ)
    (allocation : α → α → ℕ) (xs : List α) (h : ∀ a b, allocation a b ≤ (equal a b).2) :
    queryEraseAllocation equal allocation xs ≤ (queryEraseWithWork equal xs).2 :=
  queryEraseLoopAllocation_le_work equal allocation xs [] h



theorem queryInsertAllocation_le_work {α : Type*} (le : α → α → Bool × ℕ)
    (allocation : α → α → ℕ) (a : α) (xs : List α) (h : ∀ b, allocation a b ≤ (le a b).2) :
    queryInsertAllocation le allocation a xs ≤ (queryInsertWithWork le a xs).2 := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    have hb := h b
    simp only [queryInsertAllocation, queryInsertWithWork]
    split_ifs <;> dsimp only
    · exact Nat.add_le_add_right hb 2
    · calc
        _ = (allocation a b + queryInsertAllocation le allocation a xs) + 1 := (Nat.add_assoc _ _ _).symm
        _ ≤ _ := Nat.add_le_add (Nat.add_le_add hb ih) (by decide : 1 ≤ 2)



theorem querySortAllocation_le_work {α : Type*} (le : α → α → Bool × ℕ)
    (allocation : α → α → ℕ) (xs : List α) (h : ∀ a b, allocation a b ≤ (le a b).2) :
    querySortAllocation le allocation xs ≤ (querySortWithWork le xs).2 := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons a xs ih =>
    have hi := queryInsertAllocation_le_work le allocation a (querySortWithWork le xs).1 (h a)
    simp only [querySortAllocation, querySortWithWork]
    exact (Nat.add_le_add ih hi).trans (Nat.le_succ _)



theorem queryOrderedInputsAllocation_le_work {α : Type*} (equal le : α → α → Bool × ℕ)
    (equalAllocation leAllocation : α → α → ℕ) (xs : List α)
    (he : ∀ a b, equalAllocation a b ≤ (equal a b).2)
    (hl : ∀ a b, leAllocation a b ≤ (le a b).2) :
    queryOrderedInputsAllocation equal le equalAllocation leAllocation xs ≤
      (queryOrderedInputsWithWork equal le xs).2 := by
  have he' := queryEraseAllocation_le_work equal equalAllocation xs he
  have hl' := querySortAllocation_le_work le leAllocation (queryEraseWithWork equal xs).1 hl
  unfold queryOrderedInputsAllocation queryOrderedInputsWithWork
  dsimp only
  omega

end EditApproximation

end OAI
