import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionBoundedTrial
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationStreamWork

namespace OAI

/-! # The compression trial's stored arrays and exact exponent margins

Every bound below concerns actual list lengths. Repeated raw weights remain
separate occurrences; only the seven block lists are compacted.
-/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators

def compressionRawHalfSize (n : ℕ) (i : Fin 2) : ℕ :=
  if i = 0 then compressionRightRawSize n / 2
  else compressionRightRawSize n - compressionRightRawSize n / 2

theorem compressionRightRaw_card (n : ℕ) (i : Fin 2) :
    (compressionRightRaw n i).card = compressionRawHalfSize n i := by
  have hr : compressionRightRawSize n ≤ n := by unfold compressionRightRawSize; omega
  unfold compressionRightRaw compressionRawHalfSize
  split <;> apply indexInterval_card <;> omega

theorem compressionRawHalfSize_add (n : ℕ) :
    compressionRawHalfSize n 0 + compressionRawHalfSize n 1 = compressionRightRawSize n := by
  simp only [compressionRawHalfSize, ↓reduceIte, Fin.isValue, one_ne_zero]
  omega

theorem compression_cap_rate {n : ℕ} (hn : 40 ≤ n) :
    (compressionCapExponent n : ℝ) ≤ (9 / 80 : ℝ) * n := by
  have hs := mixerSize_bounds n
  have he : (mixerSize n : ℝ) = 2 * compressionHalfSize n := by
    rw [compressionHalfSize_eq]
    simp only [mixerSize, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [he] at hs
  have hnR : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have hnonneg : 0 ≤ (compressionHalfSize n : ℝ) - (3 / 400 : ℝ) * n := by
    linarith [hs.1]
  have ha : (compressionCapExponent n : ℝ) ≤
      (compressionHalfSize n : ℝ) - (3 / 400 : ℝ) * n := Nat.floor_le hnonneg
  linarith [hs.2]

theorem compression_leftRaw_rate (n : ℕ) :
    (compressionLeftRawSize n : ℝ) ≤ (11 / 100 : ℝ) * n + 29 := by
  have hs := mixerSize_bounds n
  have he : (mixerSize n : ℝ) = 2 * compressionHalfSize n := by
    rw [compressionHalfSize_eq]
    simp only [mixerSize, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [he] at hs
  have hr : (n : ℝ) < 20 * ((n / 20 : ℕ) + 1 : ℝ) := by
    exact_mod_cast (show n < 20 * (n / 20 + 1) by omega)
  have hf := compression_layout_feasible n
  have hsum : compressionLeftRawSize n + 7 * compressionHalfSize n +
      compressionRightRawSize n = n := by unfold compressionLeftRawSize; omega
  have hsumR : (compressionLeftRawSize n : ℝ) + 7 * compressionHalfSize n +
      (n / 20 : ℕ) = n := by exact_mod_cast hsum
  linarith [hs.1]

theorem compression_rawHalf_rate (n : ℕ) (i : Fin 2) :
    (compressionRawHalfSize n i : ℝ) ≤ (1 / 40 : ℝ) * n + 1 / 2 := by
  have hr : 20 * compressionRightRawSize n ≤ n := by
    unfold compressionRightRawSize
    omega
  have hh : 2 * compressionRawHalfSize n i ≤ compressionRightRawSize n + 1 := by
    unfold compressionRawHalfSize
    split <;> omega
  have hrR : (20 : ℝ) * compressionRightRawSize n ≤ n := by exact_mod_cast hr
  have hhR : (2 : ℝ) * compressionRawHalfSize n i ≤ compressionRightRawSize n + 1 := by
    exact_mod_cast hh
  linarith

theorem compression_right_product_rate {n : ℕ} (hn : 40 ≤ n) :
    ((4 * compressionCapExponent n + compressionRightRawSize n : ℕ) : ℝ) ≤
      (n : ℝ) / 2 := by
  have ha := compression_cap_rate hn
  have hr : (compressionRightRawSize n : ℝ) ≤ (n : ℝ) / 20 := by
    have h : 20 * compressionRightRawSize n ≤ n := by
      unfold compressionRightRawSize
      omega
    have hR : (20 : ℝ) * compressionRightRawSize n ≤ n := by exact_mod_cast h
    linarith
  push_cast
  linarith

theorem compression_regeneration_exponents {n : ℕ} (hn : 2000 ≤ n) :
    ((compressionPrimeExponent n + 2 * compressionCapExponent n : ℕ) : ℝ) ≤ (n : ℝ) / 2 ∧
    ((compressionPrimeExponent n + compressionCapExponent n + compressionLeftRawSize n : ℕ) : ℝ) ≤
      (n : ℝ) / 2 ∧
    (∀ i, ((compressionPrimeExponent n + 2 * compressionCapExponent n +
      compressionRawHalfSize n i : ℕ) : ℝ) ≤ (n : ℝ) / 2) ∧
    ((3 * compressionCapExponent n + compressionLeftRawSize n : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
  have ha := compression_cap_rate (by omega : 40 ≤ n)
  have hl := compression_leftRaw_rate n
  have hp : (compressionPrimeExponent n : ℝ) ≤ (249 / 1000 : ℝ) * n := by
    have h : 1000 * compressionPrimeExponent n ≤ 249 * n := by
      unfold compressionPrimeExponent
      omega
    have hR : (1000 : ℝ) * compressionPrimeExponent n ≤ 249 * n := by exact_mod_cast h
    linarith
  have hnR : (2000 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · push_cast; linarith
  · push_cast; linarith
  · intro i
    have hh := compression_rawHalf_rate n i
    push_cast
    linarith
  · have h := compression_left_exponent (by omega : 40 ≤ n)
    linarith

private theorem pow_cast_le {k : ℕ} {r : ℝ} (h : (k : ℝ) ≤ r) :
    ((2 ^ k : ℕ) : ℝ) ≤ (2 : ℝ) ^ r := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h

namespace CompressionData

variable {n : ℕ} (D : CompressionData n)

theorem compact_length_bound (e : Equiv.Perm (Fin n)) (he : D.compactTests e = true)
    (i : Fin 7) :
    (compactWeightList D.weights (D.block e i)).length ≤ 2 ^ compressionCapExponent n := by
  have h := (of_decide_eq_true he) i
  rwa [CompressionSetup.executableCapExponent_eq] at h

theorem leftRaw_card (e : Equiv.Perm (Fin n)) :
    (D.leftRaw e).card = compressionLeftRawSize n := by
  simp only [leftRaw, permuteSubset, Finset.card_map, compressionLeftRaw_card]

theorem rightRaw_card (e : Equiv.Perm (Fin n)) (i : Fin 2) :
    (D.rightRaw e i).card = compressionRawHalfSize n i := by
  simp only [rightRaw, permuteSubset, Finset.card_map, compressionRightRaw_card]

theorem storedFirst_length_bound (e : Equiv.Perm (Fin n)) (he : D.compactTests e = true)
    (i : Fin 4) : (D.storedFirst e i).length ≤ 2 ^ compressionCapExponent n := by
  fin_cases i <;> exact D.compact_length_bound e he _

theorem storedSecond_length_bounds (e : Equiv.Perm (Fin n)) (he : D.compactTests e = true) :
    (D.storedSecond e 0).length ≤ 2 ^ compressionCapExponent n ∧
    (D.storedSecond e 1).length = 2 ^ compressionLeftRawSize n ∧
    (D.storedSecond e 2).length ≤
      2 ^ (compressionCapExponent n + compressionRawHalfSize n 0) ∧
    (D.storedSecond e 3).length ≤
      2 ^ (compressionCapExponent n + compressionRawHalfSize n 1) := by
  refine ⟨D.compact_length_bound e he 5, ?_, ?_, ?_⟩
  · change (rawWeightList D.weights (D.leftRaw e)).length = _
    rw [rawWeightList_length, D.leftRaw_card]
  · change (pairSumList _ _).length ≤ _
    rw [pairSumList_length, rawWeightList_length, D.rightRaw_card, pow_add]
    exact Nat.mul_le_mul_right _ (D.compact_length_bound e he 1)
  · change (pairSumList _ _).length ≤ _
    rw [pairSumList_length, rawWeightList_length, D.rightRaw_card, pow_add]
    exact Nat.mul_le_mul_right _ (D.compact_length_bound e he 3)

theorem streamLength_bounds (e : Equiv.Perm (Fin n)) (he : D.compactTests e = true) :
    D.streamLength e 0 ≤ 2 ^ (2 * compressionCapExponent n) ∧
    D.streamLength e 1 ≤ 2 ^ (compressionCapExponent n + compressionLeftRawSize n) ∧
    D.streamLength e 2 ≤ 2 ^ (2 * compressionCapExponent n + compressionRawHalfSize n 0) ∧
    D.streamLength e 3 ≤ 2 ^ (2 * compressionCapExponent n + compressionRawHalfSize n 1) := by
  have hs := D.storedSecond_length_bounds e he
  have hf := D.storedFirst_length_bound e he
  unfold streamLength
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert Nat.mul_le_mul (hf 0) hs.1 using 1
    rw [← pow_add]
    congr 1
    omega
  · rw [hs.2.1, pow_add]
    exact Nat.mul_le_mul_right _ (hf 1)
  · convert Nat.mul_le_mul (hf 2) hs.2.2.1 using 1
    rw [← pow_add]
    congr 1
    omega
  · convert Nat.mul_le_mul (hf 3) hs.2.2.2 using 1
    rw [← pow_add]
    congr 1
    omega

theorem stream_products (e : Equiv.Perm (Fin n)) (he : D.compactTests e = true) :
    D.streamLength e 0 * D.streamLength e 1 ≤
      2 ^ (3 * compressionCapExponent n + compressionLeftRawSize n) ∧
    D.streamLength e 2 * D.streamLength e 3 ≤
      2 ^ (4 * compressionCapExponent n + compressionRightRawSize n) := by
  have h := D.streamLength_bounds e he
  constructor
  · convert Nat.mul_le_mul h.1 h.2.1 using 1
    rw [← pow_add]
    congr 1
    omega
  · convert Nat.mul_le_mul h.2.2.1 h.2.2.2 using 1
    rw [← pow_add]
    congr 1
    have hh := compressionRawHalfSize_add n
    omega

theorem prime_regeneration_bound (e : Equiv.Perm (Fin n)) (he : D.compactTests e = true)
    (hn : 2000 ≤ n) (q : CompressionSetup.PrimeSpace n) (i : Fin 4) :
    (q.val * D.streamLength e i : ℕ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) := by
  have hq : q.val ≤ 2 ^ compressionPrimeExponent n :=
    Nat.le_of_mem_primesLE (Finset.mem_filter.mp q.property).1
  have hs := D.streamLength_bounds e he
  have hx := compression_regeneration_exponents hn
  fin_cases i
  · apply (Nat.cast_le.mpr (Nat.mul_le_mul hq hs.1)).trans
    rw [← pow_add]
    exact pow_cast_le hx.1
  · apply (Nat.cast_le.mpr (Nat.mul_le_mul hq hs.2.1)).trans
    rw [← pow_add]
    apply pow_cast_le
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_assoc] using hx.2.1
  · apply (Nat.cast_le.mpr (Nat.mul_le_mul hq hs.2.2.1)).trans
    rw [← pow_add]
    apply pow_cast_le
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_assoc] using hx.2.2.1 0
  · apply (Nat.cast_le.mpr (Nat.mul_le_mul hq hs.2.2.2)).trans
    rw [← pow_add]
    apply pow_cast_le
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_assoc] using hx.2.2.1 1

theorem matching_product_bound (e : Equiv.Perm (Fin n)) (he : D.compactTests e = true)
    (hn : 2000 ≤ n) :
    (D.streamLength e 0 * D.streamLength e 1 : ℕ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) ∧
    (D.streamLength e 2 * D.streamLength e 3 : ℕ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) := by
  have h := D.stream_products e he
  exact ⟨(Nat.cast_le.mpr h.1).trans (pow_cast_le (compression_regeneration_exponents hn).2.2.2),
    (Nat.cast_le.mpr h.2).trans (pow_cast_le (compression_right_product_rate (by omega)))⟩

theorem stored_lists_small (e : Equiv.Perm (Fin n)) (he : D.compactTests e = true)
    (hn : 2000 ≤ n) (i : Fin 4) :
    ((D.storedFirst e i).length : ℝ) ≤ (2 : ℝ) ^ ((7 / 50 : ℝ) * n) ∧
    ((D.storedSecond e i).length : ℝ) ≤ (2 : ℝ) ^ ((7 / 50 : ℝ) * n) := by
  have ha := compression_cap_rate (by omega : 40 ≤ n)
  have hl := compression_leftRaw_rate n
  have hnR : (2000 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨(Nat.cast_le.mpr (D.storedFirst_length_bound e he i)).trans (pow_cast_le (by linarith)), ?_⟩
  have hs := D.storedSecond_length_bounds e he
  fin_cases i
  · exact (Nat.cast_le.mpr hs.1).trans (pow_cast_le (by linarith))
  · change ((D.storedSecond e 1).length : ℝ) ≤ _
    rw [hs.2.1]
    exact pow_cast_le (by linarith)
  · apply (Nat.cast_le.mpr hs.2.2.1).trans (pow_cast_le ?_)
    have hh := compression_rawHalf_rate n 0
    push_cast
    linarith
  · apply (Nat.cast_le.mpr hs.2.2.2).trans (pow_cast_le ?_)
    have hh := compression_rawHalf_rate n 1
    push_cast
    linarith

theorem stored_lists_capacity (e : Equiv.Perm (Fin n)) (he : D.compactTests e = true)
    (hn : 2000 ≤ n) (i : Fin 4) :
    (D.storedFirst e i).length ≤ compressionDictionaryCapacity n ∧
    (D.storedSecond e i).length ≤ compressionDictionaryCapacity n := by
  have hs := D.stored_lists_small e he hn i
  have hnR : (2000 : ℝ) ≤ n := by exact_mod_cast hn
  have hrate : (2 : ℝ) ^ ((7 / 50 : ℝ) * n) ≤ compressionDictionaryCapacity n := by
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (show (7 / 50 : ℝ) * n ≤ (199 / 1000 : ℝ) * n - 1 by linarith)).trans
    exact compression_capacity_lower n
  exact ⟨by exact_mod_cast hs.1.trans hrate, by exact_mod_cast hs.2.trans hrate⟩

/-- A conservative count of array entries, cached tournament nodes and
constant-size row cursors, at any current state or replay snapshot. -/
def groupFootprint (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) (s : D.GroupState e q i mode) : ℕ :=
  10 * ((D.storedFirst e i).length + (D.storedRightArray e q i).size +
    Tournament.nodes s.tree + 1)

theorem groupFootprint_bound (e : Equiv.Perm (Fin n)) (he : D.compactTests e = true)
    (hn : 2000 ≤ n) (q : CompressionSetup.PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) (s : D.GroupState e q i mode) :
    D.groupFootprint e q i mode s ≤ 10 * (6 * compressionDictionaryCapacity n + 4) := by
  have hs := D.stored_lists_capacity e he hn i
  have ht := Tournament.padded_nodes_le (D.storedFirst e i).toArray.size s.tree
  have hr : (D.storedRightArray e q i).size = (D.storedSecond e i).length := by
    simp only [storedRightArray, ResidueSort.size, List.size_toArray]
  simp only [List.size_toArray] at ht
  unfold groupFootprint
  rw [hr]
  omega

end CompressionData
end LowSpaceSubsetSum

end

end OAI
