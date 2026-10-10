import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionDomains
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.StoredSeparatorQueries
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSamplerCoupling

namespace OAI

/-! # Packing a sampled fixed-size subset from a stored permutation

The first `k` permutation entries are retained as a bounded list. Each
output bit is computed by a measured membership scan.
-/

namespace LowSpaceSubsetSum.PermutationSubsetCode

variable {g : ℕ}

def prefixIndices (v : Vector (Fin g) g) (k : ℕ) : List (Fin g) :=
  ((List.finRange g).filter (fun i => decide (i.val < k))).map (fun i => v[i.val])

theorem prefix_length (v : Vector (Fin g) g) (k : ℕ) : (prefixIndices v k).length ≤ g := by
  simpa only [prefixIndices, List.length_map, List.length_finRange] using
    List.length_filter_le (fun i : Fin g => decide (i.val < k)) (List.finRange g)

theorem initial_mem (k : ℕ) (hk : k ≤ g) (i : Fin g) :
    i ∈ initialSubset g k hk ↔ i.val < k := by
  constructor
  · intro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact j.isLt
  · intro hi
    exact Finset.mem_map.mpr ⟨⟨i.val, hi⟩, Finset.mem_univ _, Fin.ext rfl⟩

theorem prefix_value (v : Vector (Fin g) g) (e : Equiv.Perm (Fin g))
    (hv : ∀ i : Fin g, v[i.val] = e i) (k : ℕ) (hk : k ≤ g) :
    (prefixIndices v k).toFinset = permuteSubset e (initialSubset g k hk) := by
  have hp : prefixIndices v k = CompressionDomains.unsorted v (initialSubset g k hk) := by
    simp only [prefixIndices, CompressionDomains.unsorted, CompressionDomains.positions, initial_mem]
  rw [hp]
  exact CompressionDomains.unsorted_source v e hv _

def pack (v : Vector (Fin g) g) (k : ℕ) : Fin (2 ^ g) × ℕ :=
  let xs := prefixIndices v k
  let out := StoredSeparatorQueries.code g (fun i => CountedWeights.member i xs)
  (⟨out.1, by
    rw [StoredSeparatorQueries.code_value]
    exact (PaddedRows.index g (fun i => (CountedWeights.member i xs).1)).isLt⟩,
    out.2 + 4 * g + 3)

theorem pack_value (v : Vector (Fin g) g) (e : Equiv.Perm (Fin g))
    (hv : ∀ i : Fin g, v[i.val] = e i) (k : ℕ) (hk : k ≤ g) :
    (pack v k).1 = SeparatorStoredMasks.code (permuteSubset e (initialSubset g k hk)) := by
  apply Fin.ext
  simp only [pack, StoredSeparatorQueries.code_value, SeparatorStoredMasks.code,
    CountedWeights.member_value]
  congr 2
  funext i
  rw [← prefix_value v e hv k hk]
  simp only [List.mem_toFinset]

theorem pack_work (v : Vector (Fin g) g) (k : ℕ) :
    (pack v k).2 ≤ 20 * (g + 1) ^ 3 := by
  have hc := StoredSeparatorQueries.code_work g (g + 1)
    (fun i => CountedWeights.member i (prefixIndices v k))
    (fun i => (CountedWeights.member_work i _).trans
      (Nat.add_le_add_right (prefix_length v k) 1))
  change _ + 4 * g + 3 ≤ _
  nlinarith only [hc, Nat.zero_le (g ^ 2), Nat.zero_le (g ^ 3)]

end LowSpaceSubsetSum.PermutationSubsetCode

end OAI
