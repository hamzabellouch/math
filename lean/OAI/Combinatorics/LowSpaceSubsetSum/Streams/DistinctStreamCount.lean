import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MergedReader
import Mathlib.Data.List.Destutter

namespace OAI

/-! # Counting distinct keys without materializing the output stream

The mutable state consists of a reader state, one previous key and a count.
Sorted keys make adjacent duplicate removal exact. The second component of
the result counts actual reader calls, including a final unsuccessful call.
-/

namespace LowSpaceSubsetSum.DistinctStreamCount

variable {α σ : Type*}

def tail (read : σ → Option (α × σ)) (key : α → ℤ) : ℕ → σ → ℤ → ℕ × ℕ
  | 0, _, _ => (0, 0)
  | k + 1, s, previous =>
    match read s with
    | none => (0, 1)
    | some (x, s') =>
      if previous = key x then
        let rest := tail read key k s' previous
        (rest.1, rest.2 + 1)
      else
        let rest := tail read key k s' (key x)
        (rest.1 + 1, rest.2 + 1)

def run (read : σ → Option (α × σ)) (key : α → ℤ) : ℕ → σ → ℕ × ℕ
  | 0, _ => (0, 0)
  | k + 1, s =>
    match read s with
    | none => (0, 1)
    | some (x, s') =>
      let rest := tail read key k s' (key x)
      (rest.1 + 1, rest.2 + 1)

theorem tail_queries (read : σ → Option (α × σ)) (key : α → ℤ)
    (k : ℕ) (s : σ) (previous : ℤ) : (tail read key k s previous).2 ≤ k := by
  induction k generalizing s previous with
  | zero => rfl
  | succ k ih =>
    simp only [tail]
    split
    · omega
    · rename_i x s' hread
      split
      · exact Nat.add_le_add_right (ih s' previous) 1
      · exact Nat.add_le_add_right (ih s' (key x)) 1

theorem run_queries (read : σ → Option (α × σ)) (key : α → ℤ)
    (k : ℕ) (s : σ) : (run read key k s).2 ≤ k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [run]
    split
    · omega
    · exact Nat.add_le_add_right (tail_queries read key k _ _) 1

theorem tail_value (read : σ → Option (α × σ)) (key : α → ℤ)
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (k : ℕ) (s : σ) (previous : ℤ) (hk : (view s).length ≤ k) :
    (tail read key k s previous).1 + 1 =
      (((view s).map key).destutter' (· ≠ ·) previous).length := by
  induction k generalizing s previous with
  | zero =>
    have he : view s = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [tail, he]
  | succ k ih =>
    have hr := hread s
    cases hs : read s with
    | none =>
      simp only [hs] at hr
      simp [tail, hs, hr]
    | some p =>
      obtain ⟨x, s'⟩ := p
      simp only [hs] at hr
      have hk' : (view s').length ≤ k := by rw [hr, List.length_cons] at hk; omega
      rw [hr, List.map_cons, List.destutter'_cons]
      by_cases he : previous = key x
      · simpa only [tail, hs, ite_eq_left he, ne_eq, he, not_true_eq_false,
          ↓reduceIte] using ih s' previous hk'
      · have hh := ih s' (key x) hk'
        simp only [ne_eq] at hh
        simp only [tail, hs, ne_eq, he, not_false_eq_true,
          ↓reduceIte, List.length_cons]
        omega

theorem run_value (read : σ → Option (α × σ)) (key : α → ℤ)
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (k : ℕ) (s : σ) (hk : (view s).length ≤ k)
    (hsort : ((view s).map key).Pairwise (· ≤ ·)) :
    (run read key k s).1 = ((view s).map key).toFinset.card := by
  have hst := hsort.destutter_eq_dedup
  have hcard : ((view s).map key).dedup.length = ((view s).map key).toFinset.card := by
    rw [← List.toFinset_card_of_nodup (List.nodup_dedup _), List.toFinset_dedup]
  rw [← hcard, ← hst]
  cases k with
  | zero =>
    have he : view s = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [run, he]
  | succ k =>
    have hr := hread s
    cases hs : read s with
    | none =>
      simp only [hs] at hr
      simp [run, hs, hr]
    | some p =>
      obtain ⟨x, s'⟩ := p
      simp only [hs] at hr
      have hk' : (view s').length ≤ k := by rw [hr, List.length_cons] at hk; omega
      simpa only [run, hs, hr, List.map_cons, List.destutter_cons'] using
        tail_value read key view hread k s' (key x) hk'

end LowSpaceSubsetSum.DistinctStreamCount

end OAI
