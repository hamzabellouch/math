import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionBucket
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.FilteredStream

namespace OAI

/-! # Concrete compressed-group streams from their two stored arrays -/

namespace LowSpaceSubsetSum

def mapReader {α β σ : Type*} (f : α → β) (read : σ → Option (α × σ))
    (s : σ) : Option (β × σ) := (read s).map (fun p => (f p.1, p.2))

theorem mapReader_law {α β σ : Type*} (f : α → β) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : RowMerge.IsReader read view) :
    RowMerge.IsReader (mapReader f read) (fun s => (view s).map f) := by
  intro s
  have h := hread s
  cases hs : read s with
  | none =>
    simp only [hs] at h
    simp [mapReader, hs, h]
  | some p =>
    obtain ⟨a, s'⟩ := p
    simp only [hs] at h
    simp [mapReader, hs, h]

namespace CompressionSetup

variable {n : ℕ} (R : CompressionSetup n)

def storedRightArray (e : Equiv.Perm (Fin n)) (q : PrimeSpace n) (i : Fin 4) : Array ℤ :=
  ResidueSort.sort (R.storedSecond e i).toArray id 1 q.val

abbrev GroupState (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) :=
  MergedReader.State (FilteredStream.key (id : ℤ → ℤ) id q.val mode)
    (FilteredStream.view (α := ℤ) (R.storedRightArray e q i))
    (Nat.clog 2 (R.storedFirst e i).toArray.size)

def groupStart (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) : R.GroupState e q i mode :=
  FilteredStream.sortedStart (R.storedFirst e i).toArray (R.storedSecond e i).toArray
    id id 1 q.val 0 (by exact_mod_cast (primeRange_prime q.property).pos) mode

def groupRead (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) :
    R.GroupState e q i mode → Option (ℤ × R.GroupState e q i mode) :=
  mapReader (fun p : ℤ × ℤ => p.1 + p.2)
    (MergedReader.next (FilteredStream.key id id q.val mode)
      (FilteredStream.read (R.storedRightArray e q i))
      (FilteredStream.view (R.storedRightArray e q i)) (FilteredStream.reader _))

def groupOutput (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) (s : R.GroupState e q i mode) : List ℤ :=
  (MergedReader.output (FilteredStream.key id id q.val mode)
    (FilteredStream.read (R.storedRightArray e q i))
    (FilteredStream.view (R.storedRightArray e q i)) s).map (fun p => p.1 + p.2)

theorem groupRead_law (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) :
    RowMerge.IsReader (R.groupRead e q i mode) (R.groupOutput e q i mode) :=
  mapReader_law _ _ _ (MergedReader.reader _ _ _ (FilteredStream.reader _))

theorem groupOutput_mem (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) (z : ℤ) :
    z ∈ R.groupOutput e q i mode (R.groupStart e q i mode) ↔ z ∈ R.groupList e i := by
  change z ∈ (MergedReader.output _ _ _
    (FilteredStream.sortedStart (R.storedFirst e i).toArray (R.storedSecond e i).toArray
      id id 1 q.val 0 _ mode)).map (fun p : ℤ × ℤ => p.1 + p.2) ↔ _
  simp only [List.mem_map]
  constructor
  · rintro ⟨p, hp, he⟩
    have h := (FilteredStream.sorted_output_mem _ _ id id 1 q.val 0 _ mode p).mp hp
    exact (mem_pairSumList _ _ _).mpr
      ⟨p.1, by simpa using h.1, p.2, by simpa using h.2.1, he⟩
  · intro hz
    obtain ⟨x, hx, y, hy, he⟩ := (mem_pairSumList _ _ _).mp hz
    refine ⟨(x, y), ?_, he⟩
    apply (FilteredStream.sorted_output_mem _ _ id id 1 q.val 0 _ mode _).mpr
    exact ⟨by simpa using hx, by simpa using hy, by simp⟩

def groupKey (q : PrimeSpace n) : FilteredStream.Mode → ℤ → ℤ
  | .direct, x => x % q.val
  | .complementary v, x => (v - x) % q.val

theorem groupOutput_sorted (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) :
    (R.groupOutput e q i mode (R.groupStart e q i mode)).Pairwise
      (fun x y => groupKey q mode x ≤ groupKey q mode y) := by
  have h := FilteredStream.sorted_output_sorted (R.storedFirst e i).toArray
    (R.storedSecond e i).toArray id id 1 q.val 0
    (by exact_mod_cast (primeRange_prime q.property).pos) mode
  change ((MergedReader.output _ _ _ _).map (fun p : ℤ × ℤ => p.1 + p.2)).Pairwise _
  rw [List.pairwise_map]
  cases mode <;> simpa only [storedRightArray, groupStart, FilteredStream.key,
    groupKey, id_eq, sub_add_eq_sub_sub] using h

theorem groupOutput_length (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) :
    (R.groupOutput e q i mode (R.groupStart e q i mode)).length =
      (R.groupList e i).length := by
  have h := congrArg Multiset.card (FilteredStream.sorted_output_bag
    (R.storedFirst e i).toArray (R.storedSecond e i).toArray id id 1 q.val 0
    (by exact_mod_cast (primeRange_prime q.property).pos) mode)
  simp only [Multiset.coe_card, Multiset.card_sum, List.length_map, id_eq,
    Int.emod_one, decide_true, List.filter_true,
    List.size_toArray, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at h
  change (List.map (fun p : ℤ × ℤ => p.1 + p.2) (MergedReader.output _ _ _ _)).length = _
  rw [List.length_map, groupList, pairSumList_length]
  exact h

end CompressionSetup

end LowSpaceSubsetSum

end OAI
