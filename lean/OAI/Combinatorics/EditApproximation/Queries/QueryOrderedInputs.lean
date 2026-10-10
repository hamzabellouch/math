import OAI.Combinatorics.EditApproximation.Queries.QueryListWork
import OAI.Combinatorics.EditApproximation.Geometry.GatheredLocalStep
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Counted insertion sorting for the distinct-key lists. The numerical
encoding determines exactly the order used by the reference query. -/

namespace EditApproximation





theorem queryInsertWithWork_value {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (le : α → α → Bool × ℕ) (hle : ∀ a b, (le a b).1 = decide (r a b))
    (a : α) (xs : List α) :
    (queryInsertWithWork le a xs).1 = List.orderedInsert r a xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [queryInsertWithWork, hle, List.orderedInsert_cons, decide_eq_true_eq]
    split <;> simp only [ih]

theorem querySortWithWork_value {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (le : α → α → Bool × ℕ) (hle : ∀ a b, (le a b).1 = decide (r a b)) (xs : List α) :
    (querySortWithWork le xs).1 = xs.insertionSort r := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [querySortWithWork, queryInsertWithWork_value r le hle, ih, List.insertionSort_cons]

theorem queryInsertWithWork_cost {α : Type*} (le : α → α → Bool × ℕ)
    (C : ℕ) (hC : ∀ a b, (le a b).2 ≤ C) (a : α) (xs : List α) :
    (queryInsertWithWork le a xs).2 ≤ (xs.length + 1) * (C + 2) := by
  induction xs with
  | nil => simp only [queryInsertWithWork, List.length_nil]; omega
  | cons b xs ih =>
    have h := hC a b
    simp only [queryInsertWithWork, List.length_cons]
    split <;> dsimp only
    · nlinarith only [h, Nat.zero_le xs.length, Nat.zero_le C]
    · nlinarith only [h, ih]

theorem querySortWithWork_cost {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (le : α → α → Bool × ℕ) (hle : ∀ a b, (le a b).1 = decide (r a b))
    (C : ℕ) (hC : ∀ a b, (le a b).2 ≤ C) (xs : List α) :
    (querySortWithWork le xs).2 ≤ (xs.length + 1) ^ 2 * (C + 3) := by
  induction xs with
  | nil => simp only [querySortWithWork, List.length_nil]; omega
  | cons a xs ih =>
    have hi := queryInsertWithWork_cost le C hC a (querySortWithWork le xs).1
    have hl : (querySortWithWork le xs).1.length = xs.length := by
      rw [querySortWithWork_value r le hle, List.length_insertionSort]
    rw [hl] at hi
    change (querySortWithWork le xs).2 + _ + 1 ≤ _
    simp only [List.length_cons]
    nlinarith only [ih, hi, Nat.zero_le xs.length, Nat.zero_le C]



theorem queryOrderedInputsWithWork_value {α : Type*} [DecidableEq α]
    (encode : α → ℕ) (hinjective : Function.Injective encode)
    (equal le : α → α → Bool × ℕ)
    (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (hle : ∀ a b, (le a b).1 = decide (encode a ≤ encode b)) (xs : List α) :
    (queryOrderedInputsWithWork equal le xs).1 = orderedInputs encode hinjective xs.toFinset := by
  let : LinearOrder α := LinearOrder.lift' encode hinjective
  have hle' : ∀ a b, (le a b).1 = decide (a ≤ b) := hle
  rw [queryOrderedInputsWithWork, querySortWithWork_value (· ≤ ·) le hle',
    queryEraseWithWork_value equal heq]
  have hd := queryEraseWithWork_nodup equal heq xs
  rw [queryEraseWithWork_value equal heq] at hd
  have hn : (xs.eraseDups.insertionSort (· ≤ ·)).Nodup :=
    (List.perm_insertionSort (· ≤ ·) xs.eraseDups).nodup_iff.mpr hd
  have hs := (List.toFinset_sort (r := (· ≤ ·)) hn).mpr
    (List.pairwise_insertionSort (· ≤ ·) xs.eraseDups)
  have hf : (xs.eraseDups.insertionSort (· ≤ ·)).toFinset = xs.toFinset := by
    ext x
    simp only [List.mem_toFinset, List.mem_insertionSort, List.mem_eraseDups]
  rw [hf] at hs
  exact hs.symm

end EditApproximation

end OAI
