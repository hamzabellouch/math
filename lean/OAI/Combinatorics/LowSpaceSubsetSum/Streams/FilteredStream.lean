import OAI.Combinatorics.LowSpaceSubsetSum.Streams.ResidueSort
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.PaddedRows

namespace OAI

/-!
# The complete executable modular pair stream

Concrete lexicographic sorting, binary slice/pivot row initialization, empty
leaf padding and tournament merging are composed here. The actual merge state
stores only its tree of constant-size row cursors. All Cartesian lists and
multisets in the statements are proof views.
-/

namespace LowSpaceSubsetSum
namespace FilteredStream

variable {α β : Type*}

inductive Mode where
  | direct
  | complementary (target : ℤ)

def key (wl : α → ℤ) (wr : β → ℤ) (P : ℤ) : Mode → (α × β) → ℤ
  | .direct, z => (wl z.1 + wr z.2) % P
  | .complementary v, z => (v - wl z.1 - wr z.2) % P

def steps (n : ℕ) : ℕ := Nat.clog 2 n + 1

theorem steps_sufficient (n : ℕ) : n < 2 ^ steps n := by
  have h := Nat.le_pow_clog (by decide : 1 < 2) n
  have hp : 0 < 2 ^ Nat.clog 2 n := by positivity
  rw [steps, pow_succ]
  omega

theorem steps_le_index_bits (N n : ℕ) (hN : N ≤ 2 ^ n) : steps N ≤ n + 1 := by
  exact Nat.add_le_add_right (Nat.clog_le_of_le_pow hN) 1

def row (right : Array β) (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right wr p) (mode : Mode) (x : α) :
    PairCursor.State α right.size :=
  match mode with
  | .direct => FilteredRow.forward right wl wr p P c (steps right.size)
      hs (steps_sufficient right.size) x
  | .complementary v => FilteredRow.reverse right wl wr p P c v (steps right.size)
      hs (steps_sufficient right.size) x

theorem row_sorted (right : Array β) (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right wr p)
    (ht : FilteredRow.SecondarySorted right wr p P) (hP : 0 < P) (mode : Mode) (x : α) :
    (PairCursor.output right (row right wl wr p P c hs mode x)).Pairwise
      (fun a b => key wl wr P mode a ≤ key wl wr P mode b) := by
  cases mode with
  | direct => exact FilteredRow.forward_sorted right wl wr p P c _ hs ht _ hP x
  | complementary v => exact FilteredRow.reverse_sorted right wl wr p P c v _ hs ht _ hP x

theorem row_perm (right : Array β) (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right wr p)
    (ht : FilteredRow.SecondarySorted right wr p P) (mode : Mode) (x : α) :
    (PairCursor.output right (row right wl wr p P c hs mode x)).Perm
      ((right.toList.filter (fun y => decide ((wl x + wr y) % p = c % p))).map (fun y => (x, y))) := by
  cases mode with
  | direct => exact FilteredRow.forward_perm right wl wr p P c _ hs ht _ x
  | complementary v => exact FilteredRow.reverse_perm right wl wr p P c v _ hs ht _ x

abbrev Cursor (right : Array β) := Option (PairCursor.State α right.size)

def read (right : Array β) : Cursor (α := α) right → Option ((α × β) × Cursor (α := α) right) :=
  PaddedRows.next (PairCursor.next right)

def view (right : Array β) : Cursor (α := α) right → List (α × β) :=
  PaddedRows.view (PairCursor.output right)

theorem reader (right : Array β) : RowMerge.IsReader (read (α := α) right) (view right) :=
  PaddedRows.reader _ _ (PairCursor.reader right)

def rowArray (left : Array α) (right : Array β) (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right wr p) (mode : Mode) : Array (PairCursor.State α right.size) :=
  left.map (row right wl wr p P c hs mode)

theorem array_sorted (left : Array α) (right : Array β) (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right wr p) (ht : FilteredRow.SecondarySorted right wr p P)
    (hP : 0 < P) (mode : Mode) (d : ℕ) (path : RowMerge.Path d) :
    (view right (PaddedRows.rows (rowArray left right wl wr p P c hs mode) d path)).Pairwise
      (fun a b => key wl wr P mode a ≤ key wl wr P mode b) := by
  apply PaddedRows.rows_sorted
  intro s hmem
  simp only [rowArray, Array.toList_map, List.mem_map] at hmem
  obtain ⟨x, _, rfl⟩ := hmem
  exact row_sorted right wl wr p P c hs ht hP mode x

def start (left : Array α) (right : Array β) (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right wr p) (ht : FilteredRow.SecondarySorted right wr p P)
    (hP : 0 < P) (mode : Mode) :
    MergedReader.State (key wl wr P mode) (view right) (Nat.clog 2 left.size) :=
  MergedReader.start (key wl wr P mode) (read right) (view right) (reader right)
    (PaddedRows.rows (rowArray left right wl wr p P c hs mode) _)
    (array_sorted left right wl wr p P c hs ht hP mode _)

theorem output_bag (left : Array α) (right : Array β) (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right wr p) (ht : FilteredRow.SecondarySorted right wr p P)
    (hP : 0 < P) (mode : Mode) :
    (MergedReader.output (key wl wr P mode) (read right) (view right)
      (start left right wl wr p P c hs ht hP mode) : Multiset (α × β)) =
      ∑ i : Fin left.size,
        ((right.toList.filter (fun y => decide ((wl left[i.val] + wr y) % p = c % p))).map
          (fun y => (left[i.val], y)) : Multiset (α × β)) := by
  rw [start, MergedReader.start_output_bag]
  have hd : (rowArray left right wl wr p P c hs mode).size ≤ 2 ^ Nat.clog 2 left.size := by
    simpa only [rowArray, Array.size_map] using Nat.le_pow_clog (by decide : 1 < 2) left.size
  change (∑ path : RowMerge.Path (Nat.clog 2 left.size),
    (PaddedRows.view (PairCursor.output right)
      (PaddedRows.rows (rowArray left right wl wr p P c hs mode) _ path) : Multiset (α × β))) = _
  rw [PaddedRows.row_bag _ _ hd]
  have hsize : (rowArray left right wl wr p P c hs mode).size = left.size := by
    simp only [rowArray, Array.size_map]
  apply Fintype.sum_equiv (finCongr hsize)
  intro i
  have hin : i.val < left.size := by rw [← hsize]; exact i.isLt
  simp only [rowArray, Array.getElem_map]
  exact Quot.sound (row_perm right wl wr p P c hs ht mode left[i.val])

def sortedStart (left : Array α) (right : Array β) (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ)
    (hP : 0 < P) (mode : Mode) :
    MergedReader.State (key wl wr P mode) (view (ResidueSort.sort right wr p P))
      (Nat.clog 2 left.size) :=
  start left (ResidueSort.sort right wr p P) wl wr p P c
    (ResidueSort.primary right wr p P) (ResidueSort.secondary right wr p P) hP mode

theorem sorted_output_bag (left : Array α) (right : Array β)
    (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ) (hP : 0 < P) (mode : Mode) :
    (MergedReader.output (key wl wr P mode) (read (ResidueSort.sort right wr p P))
      (view (ResidueSort.sort right wr p P)) (sortedStart left right wl wr p P c hP mode) :
      Multiset (α × β)) =
      ∑ i : Fin left.size,
        ((right.toList.filter (fun y => decide ((wl left[i.val] + wr y) % p = c % p))).map
          (fun y => (left[i.val], y)) : Multiset (α × β)) := by
  rw [sortedStart, output_bag]
  apply Finset.sum_congr rfl
  intro i _
  exact Quot.sound (((ResidueSort.permutation right wr p P).filter
    (fun y => decide ((wl left[i.val] + wr y) % p = c % p))).map (fun y => (left[i.val], y)))

theorem sorted_output_sorted (left : Array α) (right : Array β)
    (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ) (hP : 0 < P) (mode : Mode) :
    (MergedReader.output (key wl wr P mode) (read (ResidueSort.sort right wr p P))
      (view (ResidueSort.sort right wr p P)) (sortedStart left right wl wr p P c hP mode)).Pairwise
      (fun a b => key wl wr P mode a ≤ key wl wr P mode b) :=
  MergedReader.output_sorted _ _ _ (reader _) _

theorem state_nodes (left : Array α) (right : Array β)
    (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ) (hP : 0 < P) (mode : Mode) :
    Tournament.nodes (sortedStart left right wl wr p P c hP mode).tree + 1 ≤
      4 * (left.size + 1) := Tournament.padded_nodes_le left.size _

theorem sorted_output_mem (left : Array α) (right : Array β)
    (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ) (hP : 0 < P) (mode : Mode) (z : α × β) :
    z ∈ MergedReader.output (key wl wr P mode) (read (ResidueSort.sort right wr p P))
      (view (ResidueSort.sort right wr p P)) (sortedStart left right wl wr p P c hP mode) ↔
      z.1 ∈ left.toList ∧ z.2 ∈ right.toList ∧ (wl z.1 + wr z.2) % p = c % p := by
  change z ∈ (MergedReader.output (key wl wr P mode) (read (ResidueSort.sort right wr p P))
    (view (ResidueSort.sort right wr p P)) (sortedStart left right wl wr p P c hP mode) :
    Multiset (α × β)) ↔ _
  rw [sorted_output_bag]
  simp only [Multiset.mem_sum, Finset.mem_univ, true_and, Multiset.mem_coe,
    List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨i, y, ⟨hy, hmod⟩, heq⟩
    have hz₁ : left[i.val] = z.1 := congrArg Prod.fst heq
    have hz₂ : y = z.2 := congrArg Prod.snd heq
    subst y
    refine ⟨?_, hy, ?_⟩
    · rw [← hz₁]
      exact List.mem_iff_getElem.mpr ⟨i.val, by simp, by simp⟩
    · simpa only [hz₁] using hmod
  · rintro ⟨hx, hy, hmod⟩
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    have hin : i < left.size := by simpa only [Array.length_toList] using hi
    rw [Array.getElem_toList] at hix
    refine ⟨⟨i, hin⟩, z.2, ⟨hy, ?_⟩, ?_⟩
    · simpa only [hix] using hmod
    · exact Prod.ext hix rfl

end FilteredStream
end LowSpaceSubsetSum

end OAI
