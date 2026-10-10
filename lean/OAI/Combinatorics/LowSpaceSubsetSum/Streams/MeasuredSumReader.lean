import OAI.Combinatorics.LowSpaceSubsetSum.Streams.SumReader
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredInitialization
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredDistinctCount

namespace OAI

/-! # Executed integer-sum counting

The initializer reads the shared half-sum arrays directly. Its tournament
and the tail-recursive counter are the only evolving state; the full output
stream remains a proof view. Work includes initial rows and every key read.
-/

namespace LowSpaceSubsetSum.MeasuredSumReader

abbrev key (p : ℤ × ℤ) : ℤ × ℕ := (SumReader.key p, 1)

def read (ys : Array ℤ) (s : Option SumReader.Row) :
    Option ((ℤ × ℤ) × Option SumReader.Row) × ℕ :=
  (PaddedRows.next (SumReader.read ys) s, 6)

def front (xs ys : Array ℤ) (d : ℕ) (p : RowMerge.Path d) :
    Option (RowMerge.Front d (ℤ × ℤ) (Option SumReader.Row)) × ℕ :=
  let i := PaddedRows.measuredIndex d p
  if h : i.1 < xs.size then
    let q := read ys (some ⟨xs[i.1], 0⟩)
    (q.1.map (fun z => ⟨p, z.1, z.2⟩), i.2 + q.2 + 5)
  else (none, i.2 + 2)

theorem front_value (xs ys : Array ℤ) (d : ℕ) (p : RowMerge.Path d) :
    (front xs ys d p).1 = RowMerge.front (PaddedRows.next (SumReader.read ys)) p
      (PaddedRows.rows (SumReader.rows xs) d p) := by
  by_cases h : (PaddedRows.index d p).val < xs.size
  · simp [front, PaddedRows.measuredIndex_value, PaddedRows.rows, SumReader.rows,
      RowMerge.front, read, h]
  · simp [front, PaddedRows.measuredIndex_value, PaddedRows.rows, SumReader.rows,
      RowMerge.front, h, PaddedRows.next]

theorem front_work (xs ys : Array ℤ) (d : ℕ) (p : RowMerge.Path d) :
    (front xs ys d p).2 ≤ 4 * (d + 1) ^ 2 + 11 := by
  have hi := PaddedRows.measuredIndex_work d p
  unfold front
  dsimp only
  split <;> dsimp only [read] <;> omega

def tree (xs ys : Array ℤ) :=
  Tournament.measuredBuild
    (fun x : RowMerge.Front (Nat.clog 2 xs.size) (ℤ × ℤ) (Option SumReader.Row) => key x.value)
    (Nat.clog 2 xs.size) (front xs ys (Nat.clog 2 xs.size))

theorem tree_value (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) :
    (tree xs ys).1 = (SumReader.start xs ys hs).tree := by
  simp only [tree, Tournament.measuredBuild_value, SumReader.start,
    MergedReader.start, RowMerge.start]
  congr 1
  funext p
  exact front_value xs ys _ p

def start (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) :
    SumReader.State xs ys × ℕ :=
  let out := tree xs ys
  let source := SumReader.start xs ys hs
  have he : out.1 = source.tree := tree_value xs ys hs
  (⟨out.1, he.symm ▸ source.valid, he.symm ▸ source.aligned, he.symm ▸ source.sorted⟩, out.2)

theorem start_value (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) :
    (start xs ys hs).1 = SumReader.start xs ys hs := by
  have ext {a b : SumReader.State xs ys} (h : a.tree = b.tree) : a = b := by
    cases a
    cases b
    cases h
    rfl
  apply ext
  exact tree_value xs ys hs

theorem start_work (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) :
    (start xs ys hs).2 ≤ (4 * (Nat.clog 2 xs.size + 1) ^ 2 + 32) *
      2 ^ Nat.clog 2 xs.size := by
  have h := Tournament.measuredBuild_work
    (fun x : RowMerge.Front (Nat.clog 2 xs.size) (ℤ × ℤ) (Option SumReader.Row) => key x.value)
    1 (4 * (Nat.clog 2 xs.size + 1) ^ 2 + 11) (fun _ => le_rfl)
    (Nat.clog 2 xs.size) (front xs ys (Nat.clog 2 xs.size))
    (front_work xs ys (Nat.clog 2 xs.size))
  change (tree xs ys).2 ≤ _
  exact h.trans ((Nat.sub_le _ _).trans (Nat.mul_le_mul_right _ (by omega)))

def next (xs ys : Array ℤ) (s : SumReader.State xs ys) :
    Option ((ℤ × ℤ) × SumReader.State xs ys) × ℕ :=
  MergedReader.measuredNext key (read ys) (PaddedRows.view (SumReader.view ys))
    (PaddedRows.reader _ _ (SumReader.reader ys)) s

theorem next_value (xs ys : Array ℤ) (s : SumReader.State xs ys) :
    (next xs ys s).1 = SumReader.next xs ys s :=
  MergedReader.measuredNext_value key (read ys) (PaddedRows.view (SumReader.view ys))
    (PaddedRows.reader _ _ (SumReader.reader ys)) s

theorem next_work (xs ys : Array ℤ) (s : SumReader.State xs ys) :
    (next xs ys s).2 ≤ 10 * Nat.clog 2 xs.size + 16 := by
  have h := MergedReader.measuredNext_work key (read ys)
    (PaddedRows.view (SumReader.view ys)) (PaddedRows.reader _ _ (SumReader.reader ys))
    s 1 6 (fun _ => le_rfl) (fun _ => le_rfl)
  change (next xs ys s).2 ≤ _ at h
  omega

def count (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) : ℕ × ℕ :=
  let initial := start xs ys hs
  let out := MeasuredDistinctCount.run (next xs ys) key (xs.size * ys.size) initial.1
  (out.1, initial.2 + out.2 + 2)

theorem count_value (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) :
    (count xs ys hs).1 = (SumReader.count xs ys hs).1 := by
  simp only [count, MeasuredDistinctCount.run_value, next_value, start_value]
  rfl

theorem count_work (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) :
    (count xs ys hs).2 ≤ (4 * (Nat.clog 2 xs.size + 1) ^ 2 + 32) *
      2 ^ Nat.clog 2 xs.size + (10 * Nat.clog 2 xs.size + 21) *
      (xs.size * ys.size) + 3 := by
  have hi := start_work xs ys hs
  have hc := MeasuredDistinctCount.run_work (next xs ys) key
    (10 * Nat.clog 2 xs.size + 16) 1 (next_work xs ys) (fun _ => le_rfl)
    (xs.size * ys.size) (start xs ys hs).1
  have hc' : (MeasuredDistinctCount.run (next xs ys) key (xs.size * ys.size)
      (start xs ys hs).1).2 ≤
      (10 * Nat.clog 2 xs.size + 21) * (xs.size * ys.size) + 1 := by
    convert hc using 1
  change _ + _ + 2 ≤ _
  omega

end LowSpaceSubsetSum.MeasuredSumReader

end OAI
