import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionArrayWork

namespace OAI

/-! # Raw compression lists fit the common writable capacity

These bounds apply before the compact-list guard. Hence even a failed
compression test can materialize its raw block lists within the same space.
-/

namespace LowSpaceSubsetSum.CompressionStorageBounds

variable {n : ℕ}

theorem exponents (hn : 10000 ≤ n) :
    compressionHalfSize n ≤ 199*n/1000 ∧
    compressionLeftRawSize n ≤ 199*n/1000 ∧
    ∀ i, compressionRawHalfSize n i ≤ 199*n/1000 := by
  have hf := compression_layout_feasible n
  rw [compressionHalfSize_eq] at hf ⊢
  unfold compressionLeftRawSize compressionRawHalfSize compressionRightRawSize
  rw [compressionHalfSize_eq]
  refine ⟨by omega, by omega, ?_⟩
  intro i
  split <;> omega

theorem source_lengths (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (hn : 10000 ≤ n) :
    (∀ i, ((CompressionArrayBuild.source D e).compact i).length ≤ 199*n/1000) ∧
    (CompressionArrayBuild.source D e).left.length ≤ 199*n/1000 ∧
    ∀ i, ((CompressionArrayBuild.source D e).right i).length ≤ 199*n/1000 := by
  have h := exponents hn
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa only [CompressionArrayBuild.source, Finset.length_sort, CompressionData.block,
      permuteSubset, Finset.card_map, compressionBlock_card] using h.1
  · simpa only [CompressionArrayBuild.source, Finset.length_sort, D.leftRaw_card] using h.2.1
  · intro i
    simpa only [CompressionArrayBuild.source, Finset.length_sort, D.rightRaw_card] using h.2.2 i

theorem raw_bound (a : Fin n → ℤ) (xs : List (Fin n))
    (hx : xs.length ≤ 199*n/1000) :
    (CompressionWeights.raw a xs).1.length ≤ compressionDictionaryCapacity n := by
  rw [CompressionWeights.raw_length]
  exact Nat.pow_le_pow_right (by decide) hx

end LowSpaceSubsetSum.CompressionStorageBounds

end OAI
