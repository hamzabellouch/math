import OAI.Combinatorics.LowSpaceSubsetSum.Storage.SubsetCells
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredStoredRecords

namespace OAI

/-! # Bounded masks constructed by the measured subset generators

The returned masks retain the generated index lists. The wrapping phase
counts the old family, the new list spine, and all bounded mask payloads.
Neither phase constructs finite sets.
-/

namespace LowSpaceSubsetSum.StoredMaskCells

variable {n : ℕ}

private theorem select_length (xs ys : List (Fin n)) (k : ℕ)
    (h : ys ∈ (SubsetCells.select 1 k xs).1.1) : ys.length ≤ xs.length := by
  rw [SubsetCells.select_value, CountedSubsets.select_value] at h
  exact (List.mem_sublistsLen.mp h).1.length_le

private theorem all_length (xs ys : List (Fin n))
    (h : ys ∈ (SubsetCells.all 1 xs).1.1) : ys.length ≤ xs.length := by
  rw [SubsetCells.all_value, CountedSubsets.all_value] at h
  exact (List.mem_sublists.mp h).length_le

private theorem wrap_eq (xs ys : List (List (Fin n)))
    (hx : ∀ x ∈ xs, x.length ≤ n) (hy : ∀ y ∈ ys, y.length ≤ n) (h : xs = ys) :
    xs.attach.map (fun x => (⟨x.val, hx x.val x.property⟩ : IndexedMask n)) =
      ys.attach.map (fun y => (⟨y.val, hy y.val y.property⟩ : IndexedMask n)) := by
  subst ys
  rfl

def select (xs : List (Fin n)) (hx : xs.length ≤ n) (k : ℕ) :
    (List (IndexedMask n) × ℕ) × ℕ :=
  let out := SubsetCells.select 1 k xs
  let masks := out.1.1.attach.map fun y =>
    (⟨y.val, (select_length xs y.val k y.property).trans hx⟩ : IndexedMask n)
  ((masks, out.1.2 + out.1.1.length),
    out.2 + (n + 2) * (3 * out.1.1.length + 4))

theorem select_value (xs : List (Fin n)) (hx : xs.length ≤ n) (k : ℕ) :
    (select xs hx k).1 = IndexedMask.measuredSelected xs hx k := by
  apply Prod.ext
  · exact wrap_eq _ _ (fun y hy => (select_length xs y k hy).trans hx)
      (fun y hy => by
        rw [CountedSubsets.select_value] at hy
        exact (List.mem_sublistsLen.mp hy).1.length_le.trans hx)
      (congrArg Prod.fst (SubsetCells.select_value 1 k xs))
  · exact congrArg (fun r => r.2 + r.1.length) (SubsetCells.select_value 1 k xs)

theorem select_cells (xs : List (Fin n)) (hx : xs.length ≤ n) (k : ℕ)
    (hk : k ≤ xs.length) :
    (select xs hx k).2 ≤ 256 * (n + 2) ^ 3 * (xs.length.choose k + 1) := by
  have hgen := SubsetCells.select_cells_card 1 k xs hk
  have hlen : (SubsetCells.select 1 k xs).1.1.length = xs.length.choose k := by
    rw [SubsetCells.select_value, CountedSubsets.select_length]
  have hp : n + 2 ≤ (n + 2) ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ n+2) (by decide : 1 ≤ 3)
  have hg : (xs.length + 1) ^ 3 ≤ (n + 2) ^ 3 :=
    Nat.pow_le_pow_left (by omega) 3
  have hgen' := hgen.trans (Nat.mul_le_mul_right (xs.length.choose k)
    (Nat.mul_le_mul_left 128 hg))
  have hwrap := Nat.mul_le_mul_right (3 * xs.length.choose k + 4) hp
  change (SubsetCells.select 1 k xs).2 + _ ≤ _
  rw [hlen]
  nlinarith only [hgen', hwrap, Nat.zero_le ((n + 2) ^ 3 * xs.length.choose k)]

def all (xs : List (Fin n)) (hx : xs.length ≤ n) :
    (List (IndexedMask n) × ℕ) × ℕ :=
  let out := SubsetCells.all 1 xs
  let masks := out.1.1.attach.map fun y =>
    (⟨y.val, (all_length xs y.val y.property).trans hx⟩ : IndexedMask n)
  ((masks, out.1.2 + out.1.1.length),
    out.2 + (n + 2) * (3 * out.1.1.length + 4))

theorem all_value (xs : List (Fin n)) (hx : xs.length ≤ n) :
    (all xs hx).1 = IndexedMask.measuredAll xs hx := by
  apply Prod.ext
  · exact wrap_eq _ _ (fun y hy => (all_length xs y hy).trans hx)
      (fun y hy => by
        rw [CountedSubsets.all_value] at hy
        exact (List.mem_sublists.mp hy).length_le.trans hx)
      (congrArg Prod.fst (SubsetCells.all_value 1 xs))
  · exact congrArg (fun r => r.2 + r.1.length) (SubsetCells.all_value 1 xs)

theorem all_cells (xs : List (Fin n)) (hx : xs.length ≤ n) :
    (all xs hx).2 ≤ 32 * (n + 2) * (2 ^ xs.length + 1) := by
  have hgen := SubsetCells.all_cells 1 xs
  have hlen : (SubsetCells.all 1 xs).1.1.length = 2 ^ xs.length := by
    rw [SubsetCells.all_value, CountedSubsets.all_length]
  have hg := hgen.trans (Nat.mul_le_mul_right (2 ^ xs.length)
    (Nat.mul_le_mul_left 16 (show xs.length + 1 ≤ n + 2 by omega)))
  change (SubsetCells.all 1 xs).2 + _ ≤ _
  rw [hlen]
  nlinarith only [hg, Nat.zero_le ((n + 2) * 2 ^ xs.length)]

end LowSpaceSubsetSum.StoredMaskCells

end OAI
