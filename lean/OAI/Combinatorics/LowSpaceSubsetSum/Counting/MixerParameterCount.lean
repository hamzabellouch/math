import OAI.Combinatorics.LowSpaceSubsetSum.Streams.SumReader
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedDedup
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationIntegerParameters

namespace OAI

/-! # Exact integer mixer parameters from small stored half lists

The count streams all pair occurrences, removing adjacent equal sum keys
with constant extra state. Neither the distinct-sum set nor the full mixer
powerset is stored. The count therefore feeds the integer
ordering and prime-width formulas without a real-valued oracle.
-/

namespace LowSpaceSubsetSum.MixerParameterCount

variable {n : ℕ}

def sortedWeights (a : Fin n → ℤ) (V : Finset (Fin n)) : Array ℤ :=
  (CountedSort.sort (fun x y : ℤ => decide (x ≤ y)) (rawWeightList a V)).1.toArray

theorem sortedWeights_sorted (a : Fin n → ℤ) (V : Finset (Fin n)) :
    (sortedWeights a V).toList.Pairwise (· ≤ ·) := by
  simp only [sortedWeights, CountedSort.sort_value, List.toList_toArray]
  simpa only [decide_eq_true_eq] using
    (List.pairwise_mergeSort (le := fun x y : ℤ => decide (x ≤ y))
      (fun x y z hxy hyz => decide_eq_true (le_trans (of_decide_eq_true hxy) (of_decide_eq_true hyz)))
      (fun x y => by simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total x y)
      (rawWeightList a V))

theorem sortedWeights_mem (a : Fin n → ℤ) (V : Finset (Fin n)) (x : ℤ) :
    x ∈ (sortedWeights a V).toList ↔ x ∈ distinctSums a V := by
  simp only [sortedWeights, CountedSort.sort_value, List.toList_toArray,
    (List.mergeSort_perm (rawWeightList a V) (fun x y => decide (x ≤ y))).mem_iff]
  exact mem_rawWeightList a V x

@[simp] theorem sortedWeights_size (a : Fin n → ℤ) (V : Finset (Fin n)) :
    (sortedWeights a V).size = 2 ^ V.card := by
  simp only [sortedWeights, List.size_toArray, CountedSort.sort_value,
    List.length_mergeSort, rawWeightList_length]

def count (a : Fin n → ℤ) (V W : Finset (Fin n)) : ℕ × ℕ :=
  SumReader.count (sortedWeights a V) (sortedWeights a W) (sortedWeights_sorted a W)

theorem count_value (a : Fin n → ℤ) (V W : Finset (Fin n)) (hd : Disjoint V W) :
    (count a V W).1 = distinctSumCount a (V ∪ W) := by
  rw [count, SumReader.count_value]
  unfold distinctSumCount
  congr 1
  ext z
  simp only [List.mem_toFinset, List.mem_map]
  rw [distinctSums_union_mem_iff a V W hd]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hx, hy⟩ := (SumReader.output_mem _ _ (sortedWeights_sorted a W) p).mp hp
    exact ⟨p.1, (sortedWeights_mem a V p.1).mp hx,
      p.2, (sortedWeights_mem a W p.2).mp hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    refine ⟨(x, y), ?_, rfl⟩
    exact (SumReader.output_mem _ _ (sortedWeights_sorted a W) (x, y)).mpr
      ⟨(sortedWeights_mem a V x).mpr hx, (sortedWeights_mem a W y).mpr hy⟩

theorem count_queries (a : Fin n → ℤ) (V W : Finset (Fin n)) :
    (count a V W).2 ≤ 2 ^ (V.card + W.card) := by
  simpa only [count, sortedWeights_size, pow_add] using
    SumReader.count_queries (sortedWeights a V) (sortedWeights a W) (sortedWeights_sorted a W)

def firstHalf (V : Finset (Fin n)) : Finset (Fin n) :=
  ((V.sort (· ≤ ·)).take (V.card / 2)).toFinset

def secondHalf (V : Finset (Fin n)) : Finset (Fin n) := V \ firstHalf V

theorem firstHalf_subset (V : Finset (Fin n)) : firstHalf V ⊆ V := by
  intro i hi
  exact (Finset.mem_sort (· ≤ ·)).mp
    ((List.take_sublist _ _).subset (List.mem_toFinset.mp hi))

theorem firstHalf_card (V : Finset (Fin n)) : (firstHalf V).card = V.card / 2 := by
  rw [firstHalf, List.toFinset_card_of_nodup ((Finset.sort_nodup _ _).take),
    List.length_take, Finset.length_sort]
  exact Nat.min_eq_left (Nat.div_le_self _ _)

theorem halves_union (V : Finset (Fin n)) : firstHalf V ∪ secondHalf V = V :=
  Finset.union_sdiff_of_subset (firstHalf_subset V)

theorem halves_disjoint (V : Finset (Fin n)) : Disjoint (firstHalf V) (secondHalf V) :=
  Finset.disjoint_left.mpr (fun _ hi hj => (Finset.mem_sdiff.mp hj).2 hi)

theorem secondHalf_card (V : Finset (Fin n)) :
    (secondHalf V).card = V.card - V.card / 2 := by
  rw [secondHalf, Finset.card_sdiff_of_subset (firstHalf_subset V), firstHalf_card]

/-- This function is determined entirely by the input and the permuted
mixer domain; a designated solution is not an argument. -/
def mixerCount (a : Fin n → ℤ) (V : Finset (Fin n)) : ℕ × ℕ :=
  count a (firstHalf V) (secondHalf V)

theorem mixerCount_value (a : Fin n → ℤ) (V : Finset (Fin n)) :
    (mixerCount a V).1 = distinctSumCount a V := by
  rw [mixerCount, count_value a _ _ (halves_disjoint V), halves_union]

theorem mixerCount_queries (a : Fin n → ℤ) (V : Finset (Fin n)) :
    (mixerCount a V).2 ≤ 2 ^ V.card := by
  have h := count_queries a (firstHalf V) (secondHalf V)
  rw [firstHalf_card, secondHalf_card, Nat.add_sub_of_le (Nat.div_le_self _ _)] at h
  exact h

/-- Every possible live state of the count uses only half-mixer arrays
and a tournament of half-mixer rows. -/
theorem mixerCount_footprint (a : Fin n → ℤ) (V : Finset (Fin n))
    (hc : V.card = mixerSize n)
    (s : SumReader.State (sortedWeights a (firstHalf V)) (sortedWeights a (secondHalf V))) :
    SumReader.footprint _ _ s ≤ 42 * 2 ^ (mixerSize n / 2) + 43 := by
  have h := SumReader.footprint_bound _ _ s
  have hm : mixerSize n = 2 * (mixerSize n / 2) := by unfold mixerSize; omega
  simp only [sortedWeights_size, firstHalf_card, secondHalf_card, hc] at h
  have he : mixerSize n - mixerSize n / 2 = mixerSize n / 2 := by omega
  rw [he] at h
  omega

end LowSpaceSubsetSum.MixerParameterCount

end OAI
