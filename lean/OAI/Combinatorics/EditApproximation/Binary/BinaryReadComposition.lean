import OAI.Combinatorics.EditApproximation.Binary.BinaryFiniteLoops
import OAI.Combinatorics.EditApproximation.Probability.FiniteEnumerationWork

namespace OAI

/-! Callback work is retained when a finite loop is supplied with a
costed reader. These lemmas compare the literal loop counters, so a
lookup cannot disappear when its returned word is passed to arithmetic. -/

namespace EditApproximation

theorem arithmeticMapWithWork_extra {α β : Type*} (read plain : α → β × ℕ)
    (extra : α → ℕ) (xs : List α)
    (hvalue : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hcost : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 + extra x) :
    (arithmeticMapWithWork read xs).1 = (arithmeticMapWithWork plain xs).1 ∧
      (arithmeticMapWithWork read xs).2 ≤
        (arithmeticMapWithWork plain xs).2 + (xs.map extra).sum := by
  have costBound (a a' b b' A B : ℕ) (ha : a ≤ a' + A) (hb : b ≤ b' + B) :
      a + b + 3 ≤ a' + b' + 3 + (A + B) := by
    omega
  induction xs with
  | nil => exact ⟨rfl, Nat.le_refl _⟩
  | cons x xs ih =>
    have hv := hvalue x List.mem_cons_self
    have hc := hcost x List.mem_cons_self
    have ht := ih (fun y hy => hvalue y (List.mem_cons_of_mem _ hy))
      (fun y hy => hcost y (List.mem_cons_of_mem _ hy))
    constructor
    · change (read x).1 :: (arithmeticMapWithWork read xs).1 =
        (plain x).1 :: (arithmeticMapWithWork plain xs).1
      rw [hv, ht.1]
    · change (read x).2 + (arithmeticMapWithWork read xs).2 + 3 ≤
        (plain x).2 + (arithmeticMapWithWork plain xs).2 + 3 + (extra x + (xs.map extra).sum)
      exact costBound _ _ _ _ _ _ hc ht.2

theorem arithmeticFlatMapWithWork_extra {α β : Type*} (read plain : α → List β × ℕ)
    (extra : α → ℕ) (xs : List α)
    (hvalue : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hcost : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 + extra x) :
    (arithmeticFlatMapWithWork read xs).1 = (arithmeticFlatMapWithWork plain xs).1 ∧
      (arithmeticFlatMapWithWork read xs).2 ≤
        (arithmeticFlatMapWithWork plain xs).2 + (xs.map extra).sum := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [arithmeticFlatMapWithWork, List.map_nil, List.sum_nil, Nat.add_zero, le_refl]⟩
  | cons x xs ih =>
    have hv := hvalue x List.mem_cons_self
    have hc := hcost x List.mem_cons_self
    have ht := ih (fun y hy => hvalue y (List.mem_cons_of_mem _ hy))
      (fun y hy => hcost y (List.mem_cons_of_mem _ hy))
    constructor
    · simp only [arithmeticFlatMapWithWork, hv, ht.1]
    · simp only [arithmeticFlatMapWithWork, hv, List.map_cons, List.sum_cons]
      omega

theorem filterWithWork_extra {α : Type*} (read plain : α → Bool × ℕ)
    (extra : α → ℕ) (xs : List α)
    (hvalue : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hcost : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 + extra x) :
    (filterWithWork read xs).1 = (filterWithWork plain xs).1 ∧
      (filterWithWork read xs).2 ≤
        (filterWithWork plain xs).2 + (xs.map extra).sum := by
  have costBound (a a' b b' A B : ℕ) (ha : a ≤ a' + A) (hb : b ≤ b' + B) :
      a + b + 3 ≤ a' + b' + 3 + (A + B) := by
    omega
  induction xs with
  | nil => exact ⟨rfl, Nat.le_refl _⟩
  | cons x xs ih =>
    have hv := hvalue x List.mem_cons_self
    have hc := hcost x List.mem_cons_self
    have ht := ih (fun y hy => hvalue y (List.mem_cons_of_mem _ hy))
      (fun y hy => hcost y (List.mem_cons_of_mem _ hy))
    constructor
    · change (if (read x).1 then x :: (filterWithWork read xs).1 else (filterWithWork read xs).1) =
        (if (plain x).1 then x :: (filterWithWork plain xs).1 else (filterWithWork plain xs).1)
      rw [hv, ht.1]
    · change (read x).2 + (filterWithWork read xs).2 + 3 ≤
        (plain x).2 + (filterWithWork plain xs).2 + 3 + (extra x + (xs.map extra).sum)
      exact costBound _ _ _ _ _ _ hc ht.2

theorem sum_map_le_length_mul {α : Type*} (xs : List α) (f : α → ℕ) (C : ℕ)
    (h : ∀ x ∈ xs, f x ≤ C) : (xs.map f).sum ≤ xs.length * C := by
  induction xs with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul, le_refl]
  | cons x xs ih =>
    have hh := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem arithmeticFlatMapWithWork_factor {α β : Type*} (read plain : α → List β × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hvalue : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hcost : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (arithmeticFlatMapWithWork read xs).1 = (arithmeticFlatMapWithWork plain xs).1 ∧
      (arithmeticFlatMapWithWork read xs).2 ≤ (arithmeticFlatMapWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [arithmeticFlatMapWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hv := hvalue x List.mem_cons_self
    have hc := hcost x List.mem_cons_self
    have ht := ih (fun y hy => hvalue y (List.mem_cons_of_mem _ hy))
      (fun y hy => hcost y (List.mem_cons_of_mem _ hy))
    constructor
    · simp only [arithmeticFlatMapWithWork, hv, ht.1]
    · simp only [arithmeticFlatMapWithWork, hv]
      have hl : (plain x).1.length ≤ (plain x).1.length * K := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (plain x).1.length hK
      nlinarith only [hc, ht.2, hl, hK]

theorem filterWithWork_length_le_cost {α : Type*} (test : α → Bool × ℕ) (xs : List α) :
    xs.length ≤ (filterWithWork test xs).2 := by
  induction xs with
  | nil => simp only [List.length_nil, Nat.zero_le]
  | cons x xs ih => simp only [List.length_cons, filterWithWork]; omega

theorem arithmeticMapWithWork_length_le_cost {α β : Type*} (f : α → β × ℕ) (xs : List α) :
    xs.length ≤ (arithmeticMapWithWork f xs).2 := by
  induction xs with
  | nil => simp only [List.length_nil, Nat.zero_le]
  | cons x xs ih => simp only [List.length_cons, arithmeticMapWithWork]; omega

theorem filterWithWork_add_read {α : Type*} (test : α → Bool × ℕ)
    (readCost : α → ℕ) (xs : List α) (R : ℕ) (hR : ∀ x ∈ xs, readCost x ≤ R) :
    (filterWithWork (fun x => ((test x).1, (test x).2 + readCost x)) xs).1 =
      (filterWithWork test xs).1 ∧
    (filterWithWork (fun x => ((test x).1, (test x).2 + readCost x)) xs).2 ≤
      (filterWithWork test xs).2 * (R + 1) := by
  have h := filterWithWork_extra (fun x => ((test x).1, (test x).2 + readCost x))
    test readCost xs (fun _ _ => rfl) (fun _ _ => le_rfl)
  have hs := sum_map_le_length_mul xs readCost R hR
  have hl := filterWithWork_length_le_cost test xs
  refine ⟨h.1, ?_⟩
  nlinarith only [h.2, hs, hl]

end EditApproximation

end OAI
