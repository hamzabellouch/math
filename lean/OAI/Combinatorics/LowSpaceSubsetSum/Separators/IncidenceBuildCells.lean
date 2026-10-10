import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredFilterCells
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.StoredIncidenceBuild

namespace OAI

/-! # Live cells while building the shared incidence tables

Rows are constructed one at a time. The tail-recursive table builder
retains completed row arrays, a pointer accumulator, and one active row.
The payload counter is cached; no traversal of completed rows is needed.
-/

namespace LowSpaceSubsetSum.IncidenceBuildCells

variable {g : ℕ}

def row (test : Fin (2 ^ g) → Fin (2 ^ g) → (Bool × ℕ) × ℕ)
    (family : Array (Fin (2 ^ g))) (mask : Fin (2 ^ g)) : (Array ℕ × ℕ) × ℕ :=
  let out := MeasuredFilterCells.run (fun j : Fin family.size => test mask family[j.val])
    (List.finRange family.size)
  (((out.1.1.map Fin.val).toArray, out.1.2 + 2 * out.1.1.length + family.size + 1),
    out.2 + 4 * family.size + 8)

theorem row_value (test : Fin (2 ^ g) → Fin (2 ^ g) → (Bool × ℕ) × ℕ)
    (family : Array (Fin (2 ^ g))) (mask : Fin (2 ^ g)) :
    (row test family mask).1 = StoredIncidenceBuild.row (fun a b => (test a b).1) family mask := by
  simp only [row, MeasuredFilterCells.run_value, StoredIncidenceBuild.row]

theorem row_cells (test : Fin (2 ^ g) → Fin (2 ^ g) → (Bool × ℕ) × ℕ)
    (H : ℕ) (ht : ∀ a b, (test a b).2 ≤ H)
    (family : Array (Fin (2 ^ g))) (mask : Fin (2 ^ g)) :
    (row test family mask).2 ≤ 6 * family.size + H + 12 := by
  have h := MeasuredFilterCells.run_cells
    (fun j : Fin family.size => test mask family[j.val]) H
    (fun j => ht mask family[j.val]) (List.finRange family.size)
  simp only [List.length_finRange] at h
  change _ + 4 * family.size + 8 ≤ _
  omega

theorem row_size (test : Fin (2 ^ g) → Fin (2 ^ g) → (Bool × ℕ) × ℕ)
    (family : Array (Fin (2 ^ g))) (mask : Fin (2 ^ g)) :
    (row test family mask).1.1.size ≤ family.size := by
  rw [row_value, StoredIncidenceBuild.row_value]
  exact SeparatorIncidenceTable.table_length _ _ _

private def mapAcc {α β : Type*} (f : α → (β × ℕ) × ℕ) (payload : β → ℕ) :
    List α → List β → ℕ → ℕ → ℕ → (List β × ℕ) × ℕ
  | [], acc, work, live, peak => ((acc.reverse, work + acc.length + 1),
      max peak (live + 3 * acc.length + 8))
  | x :: xs, acc, work, live, peak =>
    let out := f x
    mapAcc f payload xs (out.1.1 :: acc) (work + out.1.2 + 3)
      (live + payload out.1.1)
      (max peak (live + 2 * (xs.length + acc.length + 1) + out.2 + 8))

private theorem mapAcc_value {α β : Type*} (f : α → (β × ℕ) × ℕ) (payload : β → ℕ)
    (xs : List α) (acc : List β) (work live peak : ℕ) :
    (mapAcc f payload xs acc work live peak).1.1 = acc.reverse ++ xs.map (fun x => (f x).1.1) := by
  induction xs generalizing acc work live peak with
  | nil => simp [mapAcc]
  | cons x xs ih => simp [mapAcc, ih, List.reverse_cons, List.append_assoc]

private theorem mapAcc_work {α β : Type*} (f : α → (β × ℕ) × ℕ) (payload : β → ℕ)
    (K : ℕ) (hf : ∀ x, (f x).1.2 ≤ K) (xs : List α) (acc : List β)
    (work live peak : ℕ) :
    (mapAcc f payload xs acc work live peak).1.2 ≤
      work + (K + 4) * xs.length + acc.length + 1 := by
  induction xs generalizing acc work live peak with
  | nil => simp [mapAcc]
  | cons x xs ih =>
    have h := ih ((f x).1.1 :: acc) (work + (f x).1.2 + 3)
      (live + payload (f x).1.1)
      (max peak (live + 2 * (xs.length + acc.length + 1) + (f x).2 + 8))
    have hx := hf x
    simp only [mapAcc, List.length_cons, Nat.mul_add, Nat.mul_one] at h ⊢
    omega

private theorem mapAcc_cells {α β : Type*} (f : α → (β × ℕ) × ℕ) (payload : β → ℕ)
    (S T : ℕ) (hs : ∀ x, payload (f x).1.1 ≤ S) (ht : ∀ x, (f x).2 ≤ T)
    (xs : List α) (acc : List β) (work live peak : ℕ) :
    (mapAcc f payload xs acc work live peak).2 ≤
      max peak (live + S * xs.length + 4 * (xs.length + acc.length) + T + 16) := by
  induction xs generalizing acc work live peak with
  | nil =>
    simp only [mapAcc, List.length_nil, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact max_le_max le_rfl (by omega)
  | cons x xs ih =>
    have h := ih ((f x).1.1 :: acc) (work + (f x).1.2 + 3)
      (live + payload (f x).1.1)
      (max peak (live + 2 * (xs.length + acc.length + 1) + (f x).2 + 8))
    have hx := hs x
    have ht' := ht x
    simp only [mapAcc, List.length_cons, Nat.mul_add, Nat.mul_one] at h ⊢
    omega

/-- Same completed table as the source builder, with an additional cell
trace; the cached payload count changes only when a row is stored. -/
def preprocess (test : Fin (2 ^ g) → Fin (2 ^ g) → (Bool × ℕ) × ℕ)
    (family : Array (Fin (2 ^ g))) : (Array (Array ℕ) × ℕ) × ℕ :=
  let out := mapAcc (row test family) (fun a => a.size + 1) (List.finRange (2 ^ g)) [] 0 0 0
  ((out.1.1.toArray, out.1.2 + 2 * 2 ^ g + 1), out.2 + 2 * 2 ^ g + 4)

theorem preprocess_value (test : Fin (2 ^ g) → Fin (2 ^ g) → (Bool × ℕ) × ℕ)
    (family : Array (Fin (2 ^ g))) :
    (preprocess test family).1.1 =
      (StoredIncidenceBuild.preprocess (fun a b => (test a b).1) family).1 := by
  rw [StoredIncidenceBuild.preprocess_value]
  apply Array.toList_inj.mp
  simp only [preprocess, mapAcc_value, List.reverse_nil, List.nil_append, List.toList_toArray,
    row_value, StoredIncidenceBuild.row_value, SeparatorIncidenceTable.preprocess,
    Array.toList_ofFn, List.ofFn_eq_map]

theorem preprocess_work (test : Fin (2 ^ g) → Fin (2 ^ g) → (Bool × ℕ) × ℕ)
    (K : ℕ) (ht : ∀ a b, (test a b).1.2 ≤ K) (family : Array (Fin (2 ^ g))) :
    (preprocess test family).1.2 ≤ ((K + 7) * family.size + 8) * 2 ^ g + 2 := by
  have h := mapAcc_work (row test family) (fun a => a.size + 1)
    ((K + 7) * family.size + 2)
    (fun mask => by rw [row_value]; exact StoredIncidenceBuild.row_work _ K ht family mask)
    (List.finRange (2 ^ g)) [] 0 0 0
  simp only [List.length_finRange, List.length_nil, Nat.zero_add, Nat.add_zero] at h
  change _ + 2 * 2 ^ g + 1 ≤ _
  nlinarith only [h]

theorem preprocess_cells (test : Fin (2 ^ g) → Fin (2 ^ g) → (Bool × ℕ) × ℕ)
    (H : ℕ) (ht : ∀ a b, (test a b).2 ≤ H) (family : Array (Fin (2 ^ g))) :
    (preprocess test family).2 ≤
      (family.size + 7) * 2 ^ g + 6 * family.size + H + 32 := by
  have h := mapAcc_cells (row test family) (fun a => a.size + 1)
    (family.size + 1) (6 * family.size + H + 12)
    (fun mask => Nat.add_le_add_right (row_size test family mask) 1)
    (fun mask => row_cells test H ht family mask) (List.finRange (2 ^ g)) [] 0 0 0
  simp only [List.length_finRange, List.length_nil, Nat.add_zero, Nat.zero_add, Nat.zero_max] at h
  change _ + 2 * 2 ^ g + 4 ≤ _
  nlinarith only [h]

end LowSpaceSubsetSum.IncidenceBuildCells

namespace LowSpaceSubsetSum.IncidenceBuildCells

variable {g : ℕ}

def arrayCells (a : Array (Array ℕ)) : ℕ := (a.toList.map (fun row => row.size + 1)).sum + 1

theorem preprocess_payload (test : Fin (2 ^ g) → Fin (2 ^ g) → (Bool × ℕ) × ℕ)
    (family : Array (Fin (2 ^ g))) :
    arrayCells (preprocess test family).1.1 ≤ 2 ^ g * (family.size + 1) + 1 := by
  rw [preprocess_value, StoredIncidenceBuild.preprocess_value]
  simp only [arrayCells, SeparatorIncidenceTable.preprocess, Array.toList_ofFn,
    List.map_ofFn, List.sum_ofFn]
  apply Nat.add_le_add_right
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Nat.add_le_add_right (SeparatorIncidenceTable.table_length family
      (fun a b => ((test a b).1).1) i) 1)
  simpa using h

def contains (a b : Fin (2 ^ g)) : (Bool × ℕ) × ℕ := (StoredIncidenceBuild.contains a b, 4)
def avoids (a b : Fin (2 ^ g)) : (Bool × ℕ) × ℕ := (StoredIncidenceBuild.avoids a b, 4)

def tables (family : Array (Fin (2 ^ g))) :
    ((Array (Array ℕ) × Array (Array ℕ)) × ℕ) × ℕ :=
  let a := preprocess contains family
  let b := preprocess avoids family
  (((a.1.1, b.1.1), a.1.2 + b.1.2 + 2),
    max a.2 (2 ^ g * (family.size + 1) + 1 + b.2) + 4)

theorem tables_value (family : Array (Fin (2 ^ g))) :
    (tables family).1.1 = (StoredIncidenceBuild.tables family).1 := by
  simp only [tables, StoredIncidenceBuild.tables, preprocess_value, contains, avoids]

theorem tables_work (family : Array (Fin (2 ^ g))) :
    (tables family).1.2 ≤ 2 * (9 * family.size + 8) * 2 ^ g + 6 := by
  have ha := preprocess_work contains 2 (fun _ _ => le_rfl) family
  have hb := preprocess_work avoids 2 (fun _ _ => le_rfl) family
  change _ + _ + 2 ≤ _
  nlinarith only [ha, hb]

private theorem one_table_cells (test : Fin (2 ^ g) → Fin (2 ^ g) → (Bool × ℕ) × ℕ)
    (ht : ∀ a b, (test a b).2 ≤ 4) (family : Array (Fin (2 ^ g)))
    (hsize : family.size ≤ 11 * 2 ^ g) :
    (preprocess test family).2 ≤ 120 * 2 ^ (2 * g) := by
  have h := preprocess_cells test 4 ht family
  have hpow : 2 ^ (2 * g) = (2 ^ g) ^ 2 := by rw [two_mul, pow_add]; ring
  have hm := Nat.mul_le_mul_right (2 ^ g) hsize
  have hM : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  have hs : 2 ^ g ≤ (2 ^ g) ^ 2 := by nlinarith only [hM]
  rw [hpow]
  nlinarith only [h, hm, hs, hsize, hM]

theorem tables_cells (family : Array (Fin (2 ^ g))) (hsize : family.size ≤ 11 * 2 ^ g) :
    (tables family).2 ≤ 160 * 2 ^ (2 * g) := by
  have ha := one_table_cells contains (fun _ _ => le_rfl) family hsize
  have hb := one_table_cells avoids (fun _ _ => le_rfl) family hsize
  have hm := Nat.mul_le_mul_right (2 ^ g) hsize
  have hM : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  have hpow : 2 ^ (2 * g) = (2 ^ g) ^ 2 := by rw [two_mul, pow_add]; ring
  have hs : 2 ^ g ≤ (2 ^ g) ^ 2 := by nlinarith only [hM]
  have hP : 2 ^ g * (family.size + 1) + 1 ≤ 13 * 2 ^ (2 * g) := by
    rw [hpow]
    nlinarith only [hm, hM, hs]
  have hmax : max (preprocess contains family).2
      (2 ^ g * (family.size + 1) + 1 + (preprocess avoids family).2) ≤
      133 * 2 ^ (2 * g) := max_le (by omega) (by omega)
  change max _ _ + 4 ≤ _
  have hpositive : 1 ≤ 2 ^ (2 * g) := Nat.one_le_two_pow
  nlinarith only [hmax, hpositive]

end LowSpaceSubsetSum.IncidenceBuildCells

end OAI
