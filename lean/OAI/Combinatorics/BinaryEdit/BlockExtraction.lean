import OAI.Combinatorics.BinaryEdit.Model
import Mathlib

namespace OAI

/-! Exact contiguous-window extraction from fixed-width block concatenations. -/

namespace TreeEdit.BinaryLower
namespace BlockExtraction

/-- A list of fixed-width blocks has the expected total length. -/
theorem length_flatten_fixed {α : Type*} (blocks : List (List α)) (B : ℕ)
    (hB : ∀ z ∈ blocks, z.length = B) : blocks.flatten.length = blocks.length * B := by
  induction blocks with
  | nil => simp
  | cons z zs ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hB
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      rw [hB.1, ih hB.2]
      ring

/-- The i-th fixed-width block is exactly the corresponding window of the
flattened list. This includes width zero. -/
theorem extract_flatten_fixed {α : Type*} (blocks : List (List α)) (B : ℕ)
    (hB : ∀ z ∈ blocks, z.length = B) (i : ℕ) (hi : i < blocks.length) :
    (blocks.flatten.drop (i * B)).take B = blocks[i] := by
  induction blocks generalizing i with
  | nil => simp at hi
  | cons z zs ih =>
      have hz : z.length = B := hB z (by simp)
      have hzs : ∀ t ∈ zs, t.length = B := fun t ht => hB t (by simp [ht])
      cases i with
      | zero =>
          simp only [Nat.zero_mul, List.drop_zero, List.flatten_cons, List.getElem_cons_zero]
          rw [← hz, List.take_left]
      | succ i =>
          have hi' : i < zs.length := by simpa using hi
          have hmul : (i + 1) * B = z.length + i * B := by rw [hz]; ring
          simp only [List.flatten_cons, List.getElem_cons_succ]
          rw [hmul, List.drop_length_add_append]
          exact ih hzs i hi'

/-- The expected length for a finite indexed family of fixed-width blocks. -/
theorem length_flatten_ofFn {α : Type*} {n B : ℕ} (blocks : Fin n → Word α B) :
    (List.ofFn (fun i => (blocks i).val)).flatten.length = n * B := by
  rw [length_flatten_fixed _ B]
  · simp
  · intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact (blocks i).property

/-- Window extraction for an indexed family of fixed-width words. -/
theorem extract_flatten_ofFn {α : Type*} {n B : ℕ}
    (blocks : Fin n → Word α B) (i : Fin n) :
    ((List.ofFn (fun j => (blocks j).val)).flatten.drop (i.val * B)).take B =
      (blocks i).val := by
  have hb : ∀ z ∈ List.ofFn (fun j => (blocks j).val), z.length = B := by
    intro z hz
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
    exact (blocks j).property
  simpa using extract_flatten_fixed (List.ofFn (fun j => (blocks j).val)) B hb
    i.val (by simp)

/-- The finite-range flatMap presentation used for rows in the manuscript. -/
def concatenate {α : Type*} {n B : ℕ} (blocks : Fin n → Word α B) : List α :=
  (List.finRange n).flatMap (fun i => (blocks i).val)

@[simp] theorem length_concatenate {α : Type*} {n B : ℕ}
    (blocks : Fin n → Word α B) : (concatenate blocks).length = n * B := by
  simpa only [concatenate, List.flatMap_def, ← List.ofFn_eq_map] using
    length_flatten_ofFn blocks

/-- Exact extraction from the finite-range flatMap presentation. -/
theorem extract_concatenate {α : Type*} {n B : ℕ}
    (blocks : Fin n → Word α B) (i : Fin n) :
    ((concatenate blocks).drop (i.val * B)).take B = (blocks i).val := by
  simpa only [concatenate, List.flatMap_def, ← List.ofFn_eq_map] using
    extract_flatten_ofFn blocks i

/-- A row is itself a word of width mB. -/
def rowWord {α : Type*} {m B : ℕ} (blocks : Fin m → Word α B) : Word α (m * B) :=
  ⟨concatenate blocks, length_concatenate blocks⟩

/-- Concatenation of a finite ordered array of fixed-width blocks. -/
def concatenateRows {α : Type*} {T m B : ℕ}
    (blocks : Fin T → Fin m → Word α B) : List α :=
  (List.finRange T).flatMap fun a =>
    (List.finRange m).flatMap fun i => (blocks a i).val

@[simp] theorem length_concatenateRows {α : Type*} {T m B : ℕ}
    (blocks : Fin T → Fin m → Word α B) :
    (concatenateRows blocks).length = T * (m * B) := by
  exact length_concatenate (fun a => rowWord (blocks a))

/-- Taking the a-th row of the nested concatenation recovers that precise row. -/
theorem extract_row {α : Type*} {T m B : ℕ}
    (blocks : Fin T → Fin m → Word α B) (a : Fin T) :
    ((concatenateRows blocks).drop (a.val * (m * B))).take (m * B) =
      concatenate (blocks a) := by
  exact extract_concatenate (fun a => rowWord (blocks a)) a

/-- Extracting a cell after its row recovers the original source block. -/
theorem extract_cell_in_row {α : Type*} {T m B : ℕ}
    (blocks : Fin T → Fin m → Word α B) (a : Fin T) (i : Fin m) :
    ((((concatenateRows blocks).drop (a.val * (m * B))).take (m * B)).drop
      (i.val * B)).take B = (blocks a i).val := by
  rw [extract_row]
  exact extract_concatenate (blocks a) i

/-- Nested windows agree with direct extraction whenever the inner window
fits in the outer one. -/
theorem nested_window {α : Type*} (x : List α) (A L a b : ℕ)
    (hfit : a + b ≤ L) :
    ((((x.drop A).take L).drop a).take b) = (x.drop (A + a)).take b := by
  rw [List.drop_take, List.take_take, List.drop_drop]
  rw [Nat.min_eq_left (show b ≤ L - a by omega)]

/-- Direct extraction of any cell at its absolute position in the array. -/
theorem extract_cell {α : Type*} {T m B : ℕ}
    (blocks : Fin T → Fin m → Word α B) (a : Fin T) (i : Fin m) :
    ((concatenateRows blocks).drop ((a.val * m + i.val) * B)).take B =
      (blocks a i).val := by
  have hfit : i.val * B + B ≤ m * B := by
    have hi : i.val + 1 ≤ m := i.isLt
    nlinarith
  have h := extract_cell_in_row blocks a i
  rw [nested_window _ _ _ _ _ hfit] at h
  have hoff : a.val * (m * B) + i.val * B = (a.val * m + i.val) * B := by ring
  simpa only [hoff] using h

end BlockExtraction
end TreeEdit.BinaryLower

end OAI
