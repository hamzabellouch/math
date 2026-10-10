import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PermutationArray
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionArrayBuild

namespace OAI

/-! # Constructing the ten compression domains from a permutation array

The scan reads each domain's original positions, maps them by one array
lookup, and sorts the resulting indices into the canonical order expected
by raw subset enumeration.
-/

namespace LowSpaceSubsetSum.CompressionDomains

variable {n : ℕ}

def positions (S : Finset (Fin n)) : List (Fin n) :=
  (List.finRange n).filter (fun i => decide (i ∈ S))

def unsorted (v : Vector (Fin n) n) (S : Finset (Fin n)) : List (Fin n) :=
  (positions S).map (fun i => v[i.val])

theorem positions_length (S : Finset (Fin n)) : (positions S).length ≤ n := by
  simpa only [positions, List.length_finRange] using
    List.length_filter_le (fun i => decide (i ∈ S)) (List.finRange n)

theorem unsorted_source (v : Vector (Fin n) n) (e : Equiv.Perm (Fin n))
    (hv : ∀ i : Fin n, v[i.val] = e i) (S : Finset (Fin n)) :
    (unsorted v S).toFinset = permuteSubset e S := by
  ext x
  simp only [unsorted, List.mem_toFinset, List.mem_map, positions, List.mem_filter,
    List.mem_finRange, true_and, decide_eq_true_eq, permuteSubset, Finset.mem_map]
  simp_rw [hv]
  rfl

theorem unsorted_nodup (v : Vector (Fin n) n) (e : Equiv.Perm (Fin n))
    (hv : ∀ i : Fin n, v[i.val] = e i) (S : Finset (Fin n)) : (unsorted v S).Nodup := by
  unfold unsorted
  have hf : (fun i : Fin n => v[i.val]) = e := funext hv
  rw [hf]
  exact (List.nodup_finRange n).filter _ |>.map e.injective

def domain (v : Vector (Fin n) n) (S : Finset (Fin n)) : List (Fin n) × ℕ :=
  let xs := unsorted v S
  let sorted := MeasuredSort.sort (fun x y : Fin n => (decide (x ≤ y), 1)) xs
  (sorted.1, sorted.2 + 8 * (n + 1) ^ 2)

theorem domain_value (v : Vector (Fin n) n) (e : Equiv.Perm (Fin n))
    (hv : ∀ i : Fin n, v[i.val] = e i) (S : Finset (Fin n)) :
    (domain v S).1 = (permuteSubset e S).sort (· ≤ ·) := by
  rw [domain, MeasuredSort.sort_value]
  have hp := List.mergeSort_perm (unsorted v S) (fun x y => decide (x ≤ y))
  have hn := hp.nodup_iff.mpr (unsorted_nodup v e hv S)
  have hs := List.pairwise_mergeSort' (· ≤ ·) (unsorted v S)
  have hh := (List.toFinset_sort (r := (· ≤ ·)) hn).mpr hs
  have hset : ((unsorted v S).mergeSort (fun x y => decide (x ≤ y))).toFinset =
      permuteSubset e S := by
    have he : ((unsorted v S).mergeSort (fun x y => decide (x ≤ y))).toFinset =
        (unsorted v S).toFinset := by
      ext x
      simp only [List.mem_toFinset, hp.mem_iff]
    exact he.trans (unsorted_source v e hv S)
  rw [hset] at hh
  exact hh.symm

theorem domain_work (v : Vector (Fin n) n) (S : Finset (Fin n)) :
    (domain v S).2 ≤ 40 * (n + 1) ^ 2 := by
  have hl : (unsorted v S).length ≤ n := by
    simpa only [unsorted, List.length_map] using positions_length S
  have hpow : n ≤ 2 ^ n := (Nat.lt_two_pow_self (n := n)).le
  have hs := MeasuredSort.sort_work (fun x y : Fin n => (decide (x ≤ y), 1)) 1
    (fun _ _ => le_rfl) (unsorted v S) n (hl.trans hpow)
  change _ + 8 * (n + 1) ^ 2 ≤ _
  nlinarith only [hs, hl]

def prepare (v : Vector (Fin n) n) : CompressionArrayBuild.Blocks n × ℕ :=
  let compact := Vector.ofFn (fun i : Fin 7 => domain v (compressionBlock n i))
  let left := domain v (compressionLeftRaw n)
  let right := Vector.ofFn (fun i : Fin 2 => domain v (compressionRightRaw n i))
  (⟨fun i => compact[i.val].1, left.1, fun i => right[i.val].1⟩,
    (∑ i : Fin 7, compact[i.val].2) + left.2 + (∑ i : Fin 2, right[i.val].2) + 20)

theorem prepare_value (D : CompressionData n) (v : Vector (Fin n) n) (e : Equiv.Perm (Fin n))
    (hv : ∀ i : Fin n, v[i.val] = e i) :
    (prepare v).1 = CompressionArrayBuild.source D e := by
  simp only [prepare, Vector.getElem_ofFn, domain_value v e hv,
    CompressionArrayBuild.source, CompressionData.block, CompressionData.leftRaw,
    CompressionData.rightRaw]

theorem prepare_work (v : Vector (Fin n) n) : (prepare v).2 ≤ 500 * (n + 1) ^ 2 := by
  have hc := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 7))) =>
    domain_work v (compressionBlock n i))
  have hr := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 2))) =>
    domain_work v (compressionRightRaw n i))
  have hl := domain_work v (compressionLeftRaw n)
  have hpos : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hc hr
  simp only [prepare, Vector.getElem_ofFn, Fin.eta]
  nlinarith only [hc, hr, hl, hpos]

end LowSpaceSubsetSum.CompressionDomains

end OAI
