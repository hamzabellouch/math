import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Module.Defs

namespace OAI

namespace ArExplicit.SparseParity

variable {α : Type*}

def paired [DecidableEq α] : List α → Bool
  | [] => true
  | a :: b :: rest => decide (a = b) && paired rest
  | [_] => false

theorem sum_eq_zero_of_paired {α M : Type*} [DecidableEq α]
    [AddCommMonoid M] (hchar : ∀ x : M, x + x = 0) (f : α → M)
    (l : List α) (hl : paired l = true) : (l.map f).sum = 0 := by
  induction l using paired.induct with
  | case1 => rfl
  | case2 a b rest ih =>
    simp only [paired, Bool.and_eq_true, decide_eq_true_eq] at hl
    rcases hl with ⟨rfl, hrest⟩
    simp only [List.map_cons, List.sum_cons, ← add_assoc, hchar, zero_add]
    exact ih hrest
  | case3 a => simp [paired] at hl

def insert (cmp : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | b :: l => if cmp a b then a :: b :: l else b :: insert cmp a l

def sort (cmp : α → α → Bool) : List α → List α
  | [] => []
  | a :: l => insert cmp a (sort cmp l)

theorem sum_insert {α M : Type*} [AddCommMonoid M] (cmp : α → α → Bool)
    (f : α → M) (a : α) (l : List α) :
    ((insert cmp a l).map f).sum = f a + (l.map f).sum := by
  induction l with
  | nil => simp [insert]
  | cons b l ih =>
    simp only [insert]
    split <;> simp_all [add_left_comm]

theorem sum_sort {α M : Type*} [AddCommMonoid M] (cmp : α → α → Bool)
    (f : α → M) (l : List α) : ((sort cmp l).map f).sum = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [sort, sum_insert, ih]

theorem sum_eq_zero_of_sorted_paired {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (hchar : ∀ x : M, x + x = 0) (f : α → M) (l : List α) (cmp : α → α → Bool)
    (hl : paired (sort cmp l) = true) : (l.map f).sum = 0 := by
  rw [← sum_sort cmp f l]
  exact sum_eq_zero_of_paired hchar f _ hl

theorem module_add_self_eq_zero {k M : Type*} [Semiring k] [CharP k 2]
    [AddCommMonoid M] [Module k M] (a : M) : a + a = 0 := by
  have htwo : (2 : k) = 0 := by simpa using CharP.cast_eq_zero k 2
  rw [← two_smul k a, htwo, zero_smul]

end ArExplicit.SparseParity

end OAI
