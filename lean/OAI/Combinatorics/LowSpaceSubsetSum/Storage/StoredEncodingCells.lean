import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationKeyCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.TrieDictionaryCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredEntry

namespace OAI

/-! # Actual key construction and safe insertion scratch

The Boolean key is generated from the bounded index list. The trace includes
recursive frames, both partial bit lists and the append allocation. Keys are
computed once before the cached trie feed.
-/

namespace LowSpaceSubsetSum.StoredEncodingCells

variable {n : ℕ}

def maskIndices (mask : List (Fin n)) : List (Fin n) → (List Bool × ℕ) × ℕ
  | [] => (([], 1), 4)
  | i :: xs =>
    let hit := RepresentationKeyCells.member i mask
    let rest := maskIndices mask xs
    ((hit.1.1 :: rest.1.1, hit.1.2 + rest.1.2 + 2), max (hit.2 + 4) (rest.2 + 6))

theorem maskIndices_value (mask xs : List (Fin n)) :
    (maskIndices mask xs).1 = CountedWeights.maskIndices mask xs := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [maskIndices, CountedWeights.maskIndices, RepresentationKeyCells.member_value, ih]

theorem maskIndices_cells (mask xs : List (Fin n)) :
    (maskIndices mask xs).2 ≤ 6 * xs.length + 2 * mask.length + 8 := by
  induction xs with
  | nil => simp only [maskIndices, List.length_nil]; omega
  | cons i xs ih =>
    have hm := RepresentationKeyCells.member_cells i mask
    simp only [maskIndices, List.length_cons]
    omega

def maskBits (mask : IndexedMask n) : (List Bool × ℕ) × ℕ :=
  let out := maskIndices mask.indices (List.ofFn id)
  (out.1, out.2 + 2 * n + 4)

theorem maskBits_value (mask : IndexedMask n) :
    (maskBits mask).1 = CountedWeights.maskBits mask.indices :=
  maskIndices_value _ _

theorem maskBits_cells (mask : IndexedMask n) : (maskBits mask).2 ≤ 10 * n + 12 := by
  have h := maskIndices_cells mask.indices (List.ofFn id)
  have hm := mask.length_le
  simp only [List.length_ofFn] at h
  change (maskIndices mask.indices (List.ofFn id)).2 + 2 * n + 4 ≤ _
  omega

def bits (value : ℕ) : ℕ → ℕ → (List Bool × ℕ) × ℕ
  | 0, _ => (([], 1), 4)
  | k + 1, start =>
    let rest := bits value k (start + 1)
    ((value.testBit start :: rest.1.1, rest.1.2 + 3), rest.2 + 6)

theorem bits_value (value k start : ℕ) :
    (bits value k start).1 = CountedWeights.bits value k start := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih => simp only [bits, CountedWeights.bits, ih]

theorem bits_cells (value k start : ℕ) : (bits value k start).2 = 6 * k + 4 := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih => simp only [bits, ih]; omega

def encode (I : Instance n) (x : StoredEntry n) : (List Bool × ℕ) × ℕ :=
  let mag := bits x.value.natAbs (2 * inputScale I) 0
  let mask := maskBits x.mask
  ((decide (x.value < 0) :: (mag.1.1 ++ mask.1.1),
      mag.1.2 + mask.1.2 + 2 * inputScale I + 3),
    max mag.2 (mask.2 + 4 * inputScale I + 8) + 8 * inputScale I + 4 * n + 16)

theorem encode_value (I : Instance n) (x : StoredEntry n) :
    (encode I x).1 = StoredEntry.encode I x := by
  simp only [encode, bits_value, maskBits_value, StoredEntry.encode,
    CountedWeights.entryKey, CountedWeights.natBits]

theorem encode_cells (I : Instance n) (x : StoredEntry n) :
    (encode I x).2 ≤ 80 * inputScale I := by
  have hm := maskBits_cells x.mask
  have hn : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hb := bits_cells x.value.natAbs (2 * inputScale I) 0
  change max _ _ + 8 * inputScale I + 4 * n + 16 ≤ _
  omega

def feed (I : Instance n) (C : ℕ) (x : StoredEntry n) (r : StoredEntry.Dictionary I C) :=
  TrieDictionaryCells.safeFeed C (WeightEncoding.entryWidth I) (StoredEntry.encode I)
    (encode I) (encode_value I) (StoredEntry.encode_width I) StoredEntry.cells x r

theorem feed_value (I : Instance n) (C : ℕ) (x : StoredEntry n) (r : StoredEntry.Dictionary I C) :
    (feed I C x r).1 = CountedDictionaryCallback.feed C (WeightEncoding.entryWidth I)
      (StoredEntry.encode I) (StoredEntry.encode_width I) StoredEntry.cells x r :=
  TrieDictionaryCells.safeFeed_value _ _ _ _ _ _ _ _ _

theorem feed_cells (I : Instance n) (C : ℕ) (x : StoredEntry n) (r : StoredEntry.Dictionary I C) :
    (feed I C x r).2 ≤ 120 * inputScale I + 2 * (C + 1) + 42 := by
  have h := TrieDictionaryCells.safeFeed_cells C (WeightEncoding.entryWidth I)
    (StoredEntry.encode I) (encode I) (encode_value I) (StoredEntry.encode_width I)
    StoredEntry.cells (80 * inputScale I) (n + 2) (encode_cells I) StoredEntry.cells_le x r
  have hw := (WeightEncoding.widths_le I).2
  have hn : n + 1 ≤ inputScale I := by unfold inputScale; omega
  change (feed I C x r).2 ≤ _ at h
  omega

end LowSpaceSubsetSum.StoredEncodingCells

end OAI
