import OAI.Combinatorics.EditApproximation.Numerics.ScalarControlSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryReadComposition
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalGrid
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Fresh result-spine cells and recursive call frames for the literal
finite loops used in local continuation arithmetic. Callback footprints
are accounted separately; list elements are retained by pointer. -/

namespace EditApproximation



def arithmeticFlatMapInvocations {α β : Type*} (f : α → List β × ℕ)
    (invocations : α → ℕ) : List α → ℕ
  | [] => 1
  | x :: xs => invocations x + arithmeticFlatMapInvocations f invocations xs + 1

theorem arithmeticFlatMapAllocation_le_work {α β : Type*} (f : α → List β × ℕ)
    (allocation : α → ℕ) (xs : List α) (h : ∀ x ∈ xs, allocation x ≤ (f x).2) :
    arithmeticFlatMapAllocation f allocation xs ≤ (arithmeticFlatMapWithWork f xs).2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [arithmeticFlatMapAllocation, arithmeticFlatMapWithWork]
    omega

theorem arithmeticFlatMapInvocations_le_work_add_one {α β : Type*} (f : α → List β × ℕ)
    (invocations : α → ℕ) (xs : List α) (h : ∀ x ∈ xs, invocations x ≤ (f x).2) :
    arithmeticFlatMapInvocations f invocations xs ≤ (arithmeticFlatMapWithWork f xs).2 + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [arithmeticFlatMapInvocations, arithmeticFlatMapWithWork]
    omega



def filterInvocations {α : Type*} (invocations : α → ℕ) : List α → ℕ
  | [] => 1
  | x :: xs => invocations x + filterInvocations invocations xs + 1

theorem filterAllocation_le_work {α : Type*} (test : α → Bool × ℕ)
    (allocation : α → ℕ) (xs : List α) (h : ∀ x ∈ xs, allocation x ≤ (test x).2) :
    filterAllocation test allocation xs ≤ (filterWithWork test xs).2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [filterAllocation, filterWithWork]
    split_ifs <;> omega

theorem filterInvocations_le_work_add_one {α : Type*} (test : α → Bool × ℕ)
    (invocations : α → ℕ) (xs : List α) (h : ∀ x ∈ xs, invocations x ≤ (test x).2) :
    filterInvocations invocations xs ≤ (filterWithWork test xs).2 + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [filterInvocations, filterWithWork]
    omega



theorem filterMapAllocation_le_work {α β : Type*} (f : α → Option β × ℕ)
    (allocation : α → ℕ) (xs : List α) (h : ∀ x ∈ xs, allocation x ≤ (f x).2) :
    filterMapAllocation f allocation xs ≤ (filterMapWithWork f xs).2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [filterMapAllocation, filterMapWithWork]
    cases he : (f x).1 <;> simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem filterMapInvocations_le_work_add_one {α β : Type*} (f : α → Option β × ℕ)
    (invocations : α → ℕ) (xs : List α) (h : ∀ x ∈ xs, invocations x ≤ (f x).2) :
    filterInvocations invocations xs ≤ (filterMapWithWork f xs).2 + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [filterInvocations, filterMapWithWork]
    omega

theorem allInvocations_le_work_add_one {α : Type*} (test : α → Bool × ℕ)
    (invocations : α → ℕ) (xs : List α) (h : ∀ x ∈ xs, invocations x ≤ (test x).2) :
    filterInvocations invocations xs ≤ (allWithWork test xs).2 + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [filterInvocations, allWithWork]
    omega

end EditApproximation

end OAI
