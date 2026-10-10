import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionReader
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredInitialization
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredRow

namespace OAI

/-! # Executed compression reader initialization on shared arrays -/

namespace LowSpaceSubsetSum.CompressionInitialization

def row (right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1)
    (mode : FilteredStream.Mode) (x : ℤ) : PairCursor.State ℤ right.size × ℕ :=
  FilteredStream.measuredRow right (fun x => (x, 1)) (fun x => (x, 1)) 1 P 0 hs mode x

theorem row_value (right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1)
    (mode : FilteredStream.Mode) (x : ℤ) :
    (row right P hs mode x).1 = FilteredStream.row right id id 1 P 0 hs mode x :=
  FilteredStream.measuredRow_value _ _ _ _ _ _ _ _ _

theorem row_scale {n : ℕ} (I : Instance n) (hn : 10000 ≤ n)
    (right : Array ℤ) (P : ℤ) (hs : FilteredRow.PrimarySorted right id 1)
    (mode : FilteredStream.Mode) (x : ℤ) (hsize : right.size ≤ 2 ^ n) :
    (row right P hs mode x).2 ≤ inputScale I ^ 2 := by
  have hw := FilteredStream.measuredRow_work right (fun x => (x, 1)) (fun x => (x, 1))
    1 P 0 hs mode x 1 (fun _ => le_rfl) (fun _ => le_rfl)
  have hsteps := FilteredStream.steps_le_index_bits right.size n hsize
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  change (row right P hs mode x).2 ≤ 3 * (1 + 12) * FilteredStream.steps right.size + 1 + 16 at hw
  nlinarith only [hw, hsteps, hu, hn]

def tree (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1) (mode : FilteredStream.Mode) :=
  FilteredStream.measuredInitialTree left right (CompressionReader.key P mode)
    (row right P hs mode) (Nat.clog 2 left.size)

theorem tree_value (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1)
    (ht : FilteredRow.SecondarySorted right id 1 P) (hP : 0 < P)
    (mode : FilteredStream.Mode) :
    (tree left right P hs mode).1 = (FilteredStream.start left right id id 1 P 0 hs ht hP mode).tree := by
  simp only [tree, FilteredStream.measuredInitialTree_value, row_value,
    FilteredStream.start, MergedReader.start, FilteredStream.rowArray]

def start (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1)
    (ht : FilteredRow.SecondarySorted right id 1 P) (hP : 0 < P)
    (mode : FilteredStream.Mode) :
    CompressionReader.State P mode right (Nat.clog 2 left.size) × ℕ :=
  let out := tree left right P hs mode
  let source := FilteredStream.start left right id id 1 P 0 hs ht hP mode
  have he : out.1 = source.tree := tree_value left right P hs ht hP mode
  (⟨out.1, he.symm ▸ source.valid, he.symm ▸ source.aligned, he.symm ▸ source.sorted⟩, out.2)

theorem start_value (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1)
    (ht : FilteredRow.SecondarySorted right id 1 P) (hP : 0 < P)
    (mode : FilteredStream.Mode) :
    (start left right P hs ht hP mode).1 = FilteredStream.start left right id id 1 P 0 hs ht hP mode := by
  have ext {a b : CompressionReader.State P mode right (Nat.clog 2 left.size)}
      (h : a.tree = b.tree) : a = b := by
    cases a
    cases b
    cases h
    rfl
  apply ext
  exact tree_value left right P hs ht hP mode

theorem start_work {n : ℕ} (I : Instance n) (hn : 10000 ≤ n)
    (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1)
    (ht : FilteredRow.SecondarySorted right id 1 P) (hP : 0 < P)
    (mode : FilteredStream.Mode) (hL : left.size ≤ 2 ^ n) (hR : right.size ≤ 2 ^ n) :
    (start left right P hs ht hP mode).2 ≤ inputScale I ^ 4 * (left.size + 1) := by
  have hw := FilteredStream.measuredInitialTree_work left right (CompressionReader.key P mode)
    (row right P hs mode) 6 (inputScale I ^ 2) (fun _ => le_rfl)
    (fun x => row_scale I hn right P hs mode x hR) (Nat.clog 2 left.size)
  have hd := Nat.clog_le_of_le_pow hL
  have hsquare := Nat.pow_le_pow_left (Nat.add_le_add_right hd 1) 2
  have hp := Tournament.padded_nodes_le left.size (tree left right P hs mode).1
  rw [Tournament.nodes_exact, pow_succ] at hp
  have hpad : 2 ^ Nat.clog 2 left.size ≤ 2 * (left.size + 1) := by omega
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hnu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hn2 := Nat.pow_le_pow_left hnu 2
  have h1 : 1 ≤ inputScale I ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h112 : 112 ≤ inputScale I ^ 2 := by nlinarith only [hu]
  have hscale : 112 * inputScale I ^ 2 ≤ inputScale I ^ 4 := by
    calc
      _ ≤ inputScale I ^ 2 * inputScale I ^ 2 := Nat.mul_le_mul_right _ h112
      _ = _ := by ring
  have hpoly : 2 * (4 * (n + 1) ^ 2 + inputScale I ^ 2 + 2 * 6 + 39) ≤ inputScale I ^ 4 := by
    omega
  change (tree left right P hs mode).2 ≤ _
  calc
    _ ≤ (4 * (Nat.clog 2 left.size + 1) ^ 2 + inputScale I ^ 2 + 2 * 6 + 39) *
        2 ^ Nat.clog 2 left.size := hw
    _ ≤ (4 * (n + 1) ^ 2 + inputScale I ^ 2 + 2 * 6 + 39) *
        (2 * (left.size + 1)) := Nat.mul_le_mul (by omega) hpad
    _ = (2 * (4 * (n + 1) ^ 2 + inputScale I ^ 2 + 2 * 6 + 39)) *
        (left.size + 1) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hpoly

end LowSpaceSubsetSum.CompressionInitialization

end OAI
