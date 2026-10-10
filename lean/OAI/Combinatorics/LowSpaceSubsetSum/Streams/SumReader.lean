import OAI.Combinatorics.LowSpaceSubsetSum.Streams.PaddedRows
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.DistinctStreamCount
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionDictionary

namespace OAI

/-! # Counting a mixer through a tournament of ordinary sum rows

Only the two half-mixer arrays and a tournament of constant-size cursors
are stored. The output lists in the proofs are views, not runtime fields.
Sorting and counting use integer sums and require no modulus or real oracle.
-/

namespace LowSpaceSubsetSum.SumReader

open scoped BigOperators

structure Row where
  left : ℤ
  position : ℕ

def read (ys : Array ℤ) (s : Row) : Option ((ℤ × ℤ) × Row) :=
  if h : s.position < ys.size then
    some ((s.left, ys[s.position]), ⟨s.left, s.position + 1⟩)
  else none

def view (ys : Array ℤ) (s : Row) : List (ℤ × ℤ) :=
  (ys.toList.drop s.position).map (fun y => (s.left, y))

theorem reader (ys : Array ℤ) : RowMerge.IsReader (read ys) (view ys) := by
  intro s
  by_cases h : s.position < ys.size
  · have hlist : s.position < ys.toList.length := by simpa using h
    simp only [read, dite_eq_left h, view]
    rw [List.drop_eq_getElem_cons hlist, List.map_cons]
    rfl
  · have he : ys.toList.drop s.position = [] := List.drop_eq_nil_iff.mpr (by simpa using Nat.le_of_not_gt h)
    simp [read, h, view, he]

def key (p : ℤ × ℤ) : ℤ := p.1 + p.2

def rows (xs : Array ℤ) : Array Row := xs.map (fun x => ⟨x, 0⟩)

theorem row_sorted (ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) (s : Row) :
    (view ys s).Pairwise (fun x y => key x ≤ key y) := by
  rw [view, List.pairwise_map]
  exact (hs.sublist (List.drop_sublist s.position ys.toList)).imp
    (fun h => by dsimp only [key]; omega)

abbrev State (xs ys : Array ℤ) :=
  MergedReader.State key (PaddedRows.view (view ys)) (Nat.clog 2 xs.size)

def start (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) : State xs ys :=
  MergedReader.start key (PaddedRows.next (read ys)) (PaddedRows.view (view ys))
    (PaddedRows.reader _ _ (reader ys))
    (PaddedRows.rows (rows xs) (Nat.clog 2 xs.size))
    (PaddedRows.rows_sorted _ _ _ key (fun s _ => row_sorted ys hs s))

def next (xs ys : Array ℤ) : State xs ys → Option ((ℤ × ℤ) × State xs ys) :=
  MergedReader.next key (PaddedRows.next (read ys)) (PaddedRows.view (view ys))
    (PaddedRows.reader _ _ (reader ys))

def output (xs ys : Array ℤ) : State xs ys → List (ℤ × ℤ) :=
  MergedReader.output key (PaddedRows.next (read ys)) (PaddedRows.view (view ys))

theorem next_law (xs ys : Array ℤ) : RowMerge.IsReader (next xs ys) (output xs ys) :=
  MergedReader.reader _ _ _ (PaddedRows.reader _ _ (reader ys))

theorem output_sorted (xs ys : Array ℤ) (s : State xs ys) :
    ((output xs ys s).map key).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  exact MergedReader.output_sorted _ _ _ (PaddedRows.reader _ _ (reader ys)) s

theorem start_bag (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) :
    (output xs ys (start xs ys hs) : Multiset (ℤ × ℤ)) =
      ∑ i : Fin xs.size, ((ys.toList.map (fun y => (xs[i.val], y))) : Multiset (ℤ × ℤ)) := by
  rw [output, start, MergedReader.start_output_bag]
  calc
    _ = ∑ i : Fin (rows xs).size, (view ys (rows xs)[i.val] : Multiset (ℤ × ℤ)) :=
      PaddedRows.row_bag (rows xs) (Nat.clog 2 xs.size)
        (by simpa [rows] using Nat.le_pow_clog (by decide : 1 < 2) xs.size) (view ys)
    _ = _ := by
      apply Fintype.sum_equiv (finCongr (show (rows xs).size = xs.size by simp [rows]))
      intro i
      simp only [rows, Array.getElem_map, view, List.drop_zero]
      rfl

theorem output_mem (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) (p : ℤ × ℤ) :
    p ∈ output xs ys (start xs ys hs) ↔ p.1 ∈ xs.toList ∧ p.2 ∈ ys.toList := by
  change p ∈ (output xs ys (start xs ys hs) : Multiset (ℤ × ℤ)) ↔ _
  rw [start_bag, Multiset.mem_sum]
  simp only [Finset.mem_univ, true_and, Multiset.mem_coe, List.mem_map]
  constructor
  · rintro ⟨i, y, hy, he⟩
    obtain rfl := he
    exact ⟨List.mem_iff_getElem.mpr ⟨i.val, by simpa only [Array.length_toList] using i.isLt, by simp⟩, hy⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
    refine ⟨⟨i, by simpa using hi⟩, p.2, hy, ?_⟩
    simpa using congrArg (fun x => (x, p.2)) he

theorem output_length (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) :
    (output xs ys (start xs ys hs)).length = xs.size * ys.size := by
  have h := congrArg Multiset.card (start_bag xs ys hs)
  simpa only [Multiset.coe_card, Multiset.card_sum, List.length_map,
    Array.length_toList, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h

def count (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) : ℕ × ℕ :=
  DistinctStreamCount.run (next xs ys) key (xs.size * ys.size) (start xs ys hs)

theorem count_value (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) :
    (count xs ys hs).1 = ((output xs ys (start xs ys hs)).map key).toFinset.card :=
  DistinctStreamCount.run_value _ _ _ (next_law xs ys) _ _
    (le_of_eq (output_length xs ys hs)) (output_sorted xs ys _)

theorem count_queries (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) :
    (count xs ys hs).2 ≤ xs.size * ys.size := DistinctStreamCount.run_queries _ _ _ _

/-- Every cursor and cached front occupies a constant number of flat cells. -/
def footprint (xs ys : Array ℤ) (s : State xs ys) : ℕ :=
  xs.size + ys.size + 10 * (Tournament.nodes s.tree + 1) + 3

theorem footprint_bound (xs ys : Array ℤ) (s : State xs ys) :
    footprint xs ys s ≤ 41 * xs.size + ys.size + 43 := by
  have h := Tournament.padded_nodes_le xs.size s.tree
  unfold footprint
  omega

end LowSpaceSubsetSum.SumReader

end OAI
