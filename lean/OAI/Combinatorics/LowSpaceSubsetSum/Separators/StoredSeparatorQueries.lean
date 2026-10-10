import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredEntry
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredInitialization
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredPivot
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorEncodedCheck

namespace OAI

/-! # Stored-mask codes and executed separator interval queries

A coordinate row is an explicit vector of ambient indices. Every mask bit
is obtained by scanning the bounded stored index list. Its binary code then
indexes an already prepared incidence table. Two measured binary searches
answer the interval query without scanning that incidence list.
-/

namespace LowSpaceSubsetSum.StoredSeparatorQueries

variable {n g : ℕ}

/-- The callback is executed once for every coordinate. -/
def code : (g : ℕ) → (Fin g → Bool × ℕ) → ℕ × ℕ
  | 0, _ => (0, 1)
  | g + 1, bits =>
    let first := bits 0
    let rest := code g (fun j => bits j.succ)
    ((if first.1 then 1 else 0) + 2 * rest.1, first.2 + rest.2 + 2 * g + 6)

theorem code_value (g : ℕ) (bits : Fin g → Bool × ℕ) :
    (code g bits).1 = (PaddedRows.index g (fun j => (bits j).1)).val := by
  rw [← PaddedRows.measuredIndex_value]
  induction g with
  | zero => rfl
  | succ g ih =>
    simp only [code, PaddedRows.measuredIndex]
    rw [ih]

theorem code_work (g K : ℕ) (bits : Fin g → Bool × ℕ)
    (hb : ∀ j, (bits j).2 ≤ K) :
    (code g bits).2 ≤ (K + 6) * (g + 1) ^ 2 := by
  induction g with
  | zero => simp [code]
  | succ g ih =>
    have hr := ih (fun j => bits j.succ) (fun j => hb j.succ)
    have hf := hb 0
    change _ + _ + 2 * g + 6 ≤ _
    nlinarith only [hr, hf, Nat.zero_le g, Nat.zero_le K, Nat.zero_le (K * g)]

def localMask (row : Vector (Fin n) g) (x : StoredEntry n) : Finset (Fin g) :=
  Finset.univ.filter (fun j => row[j] ∈ x.mask.semantic)

def localCode (row : Vector (Fin n) g) (x : StoredEntry n) : Fin (2 ^ g) × ℕ :=
  let out := code g (fun j => CountedWeights.member row[j] x.mask.indices)
  (⟨out.1, by
    rw [code_value]
    exact (PaddedRows.index g (fun j =>
      (CountedWeights.member row[j] x.mask.indices).1)).isLt⟩, out.2)

theorem localCode_value (row : Vector (Fin n) g) (x : StoredEntry n) :
    (localCode row x).1 = SeparatorStoredMasks.code (localMask row x) := by
  apply Fin.ext
  simp only [localCode, code_value, SeparatorStoredMasks.code]
  congr 2
  funext j
  simp only [CountedWeights.member_value, localMask, Finset.mem_filter,
    Finset.mem_univ, true_and, IndexedMask.semantic, List.mem_toFinset]

theorem localCode_work (row : Vector (Fin n) g) (x : StoredEntry n) :
    (localCode row x).2 ≤ (n + 7) * (g + 1) ^ 2 := by
  apply code_work g (n + 1)
  intro j
  exact (CountedWeights.member_work row[j] x.mask.indices).trans
    (Nat.add_le_add_right x.mask.length_le 1)

theorem localMask_coordinates (C : TopCoordinates n g) (i : Fin 4)
    (row : Vector (Fin n) g) (hrow : ∀ j, row[j] = C.index (i, j)) (x : StoredEntry n) :
    localMask row x = SeparatorCheck.localMask i (C.encodeMask x.mask.semantic) := by
  ext j
  simp only [localMask, Finset.mem_filter, Finset.mem_univ, true_and,
    SeparatorCheck.localMask_mem, TopCoordinates.encodeMask_mem, hrow]

/-- One indexed read after computing a bounded mask's local code. -/
def lookup (row : Vector (Fin n) g) (x : StoredEntry n)
    (store : Array (Array ℕ)) (hs : store.size = 2 ^ g) : Array ℕ × ℕ :=
  let c := localCode row x
  (store[c.1.val]'(by rw [hs]; exact c.1.isLt), c.2 + 1)

theorem lookup_value (row : Vector (Fin n) g) (x : StoredEntry n)
    (store : Array (Array ℕ)) (hs : store.size = 2 ^ g) :
    (lookup row x store hs).1 =
      SeparatorStoredMasks.containsList store hs (localMask row x) := by
  simp only [lookup, localCode_value, SeparatorStoredMasks.containsList]

theorem lookup_work (row : Vector (Fin n) g) (x : StoredEntry n)
    (store : Array (Array ℕ)) (hs : store.size = 2 ^ g) :
    (lookup row x store hs).2 ≤ (n + 7) * (g + 1) ^ 2 + 1 :=
  Nat.add_le_add_right (localCode_work row x) 1

theorem contains_value (row : Vector (Fin n) g) (x : StoredEntry n)
    (family : Array (Finset (Fin g))) :
    (lookup row x (SeparatorStoredMasks.containsStore family)
      (SeparatorStoredMasks.containsStore_size family)).1 =
      SeparatorIncidenceTable.table family (fun D S => decide (D ⊆ S)) (localMask row x) := by
  rw [lookup_value, SeparatorStoredMasks.containsList_eq]

theorem avoids_value (row : Vector (Fin n) g) (x : StoredEntry n)
    (family : Array (Finset (Fin g))) :
    (lookup row x (SeparatorStoredMasks.avoidsStore family)
      (SeparatorStoredMasks.avoidsStore_size family)).1 =
      SeparatorIncidenceTable.table family (fun D S => decide (Disjoint D S)) (localMask row x) := by
  rw [lookup_value]
  exact SeparatorStoredMasks.avoidsList_eq family (localMask row x)

private theorem search_unique {m : ℕ} (p : Fin m → Bool)
    (a b : BinaryPivot.Cut m)
    (ha : ∀ i : Fin m, p i = true ↔ i.val < a.lo)
    (hb : ∀ i : Fin m, p i = true ↔ i.val < b.lo) : a.lo = b.lo := by
  have hma := a.ordered.trans a.bounded
  have hmb := b.ordered.trans b.bounded
  apply Nat.le_antisymm
  · by_contra h
    have hlt : b.lo < a.lo := by omega
    have hi : b.lo < m := hlt.trans_le hma
    have ht := (hb ⟨b.lo, hi⟩).mp ((ha ⟨b.lo, hi⟩).mpr hlt)
    exact (Nat.lt_irrefl b.lo) ht
  · by_contra h
    have hlt : a.lo < b.lo := by omega
    have hi : a.lo < m := hlt.trans_le hmb
    have ht := (ha ⟨a.lo, hi⟩).mp ((hb ⟨a.lo, hi⟩).mpr hlt)
    exact (Nat.lt_irrefl a.lo) ht

/-- The caller supplies a cached number of binary-search steps. -/
def lower (steps : ℕ) (a : Array ℕ) (r : ℕ) : ℕ × ℕ :=
  let out := BinaryPivot.measuredSearch (fun i : Fin a.size => (decide (a[i.val] < r), 2)) steps
  (out.1.lo, out.2)

theorem lower_value (steps : ℕ) (a : Array ℕ)
    (hs : Monotone (fun i : Fin a.size => a[i.val])) (hsteps : a.size < 2 ^ steps) (r : ℕ) :
    (lower steps a r).1 = SeparatorIncidenceTable.lower a r := by
  let p := fun i : Fin a.size => decide (a[i.val] < r)
  have hp : BinaryPivot.PrefixPredicate p := by
    intro i j hij hj
    exact decide_eq_true ((hs hij).trans_lt (of_decide_eq_true hj))
  change (BinaryPivot.measuredSearch (fun i : Fin a.size => (p i, 2)) steps).1.lo = _
  rw [BinaryPivot.measuredSearch_value]
  exact search_unique p _ _
    (BinaryPivot.search_exact p hp steps hsteps).2
    (BinaryPivot.search_exact p hp _ (FilteredStream.steps_sufficient a.size)).2

theorem lower_work (steps : ℕ) (a : Array ℕ) (r : ℕ) :
    (lower steps a r).2 ≤ 10 * steps := by
  exact BinaryPivot.measuredSearch_work _ 2 (fun _ => le_rfl) steps

def hit (steps : ℕ) (a : Array ℕ) (lo hi : ℕ) : Bool × ℕ :=
  let l := lower steps a lo
  let r := lower steps a hi
  (decide (l.1 < r.1), l.2 + r.2 + 3)

theorem hit_value (steps : ℕ) (a : Array ℕ)
    (hs : Monotone (fun i : Fin a.size => a[i.val])) (hsteps : a.size < 2 ^ steps)
    (lo hi : ℕ) : (hit steps a lo hi).1 = SeparatorIncidenceTable.hit a lo hi := by
  simp only [hit, lower_value steps a hs hsteps, SeparatorIncidenceTable.hit]

theorem hit_work (steps : ℕ) (a : Array ℕ) (lo hi : ℕ) :
    (hit steps a lo hi).2 ≤ 20 * steps + 3 := by
  have hl := lower_work steps a lo
  have hr := lower_work steps a hi
  change _ + _ + 3 ≤ _
  omega

end LowSpaceSubsetSum.StoredSeparatorQueries

end OAI
