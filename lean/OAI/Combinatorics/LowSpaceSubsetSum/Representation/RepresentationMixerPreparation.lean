import OAI.Combinatorics.LowSpaceSubsetSum.Counting.MixerHalfLists
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionDomains
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationProgram

namespace OAI

/-! # Preparing the three mixer domains and exact integer counts

The stored permutation is scanned to construct each sorted index list. Each
count then generates just the two half arrays and streams their pair sums.
No solution or real logarithm is an argument of this preparation.
-/

namespace LowSpaceSubsetSum.RepresentationMixerPreparation

open scoped BigOperators
variable {n : ℕ}

structure Result (n : ℕ) where
  domains : Vector (List (Fin n)) 3
  counts : Vector ℕ 3

def run (D : RepresentationData n) (v : Vector (Fin n) n) : Result n × ℕ :=
  let domains := Vector.ofFn (fun i : Fin 3 => CompressionDomains.domain v (D.mixers i))
  let counts := Vector.ofFn (fun i : Fin 3 =>
    MixerHalfLists.count (fun j => (D.input.values j : ℤ)) domains[i.val].1)
  (⟨domains.map Prod.fst, counts.map Prod.fst⟩,
    (∑ i : Fin 3, (domains[i.val].2 + counts[i.val].2)) + 12)

theorem domains_value (D : RepresentationData n) (v : Vector (Fin n) n)
    (e : Equiv.Perm (Fin n)) (hv : ∀ i : Fin n, v[i.val] = e i) (j : Fin 3) :
    (run D v).1.domains[j.val] = (permuteSubset e (D.mixers j)).sort (· ≤ ·) := by
  simp only [run, Vector.getElem_map, Vector.getElem_ofFn]
  exact CompressionDomains.domain_value v e hv (D.mixers j)

theorem counts_value (D : RepresentationData n) (v : Vector (Fin n) n)
    (e : Equiv.Perm (Fin n)) (hv : ∀ i : Fin n, v[i.val] = e i) (j : Fin 3) :
    (run D v).1.counts[j.val] =
      distinctSumCount (fun i => (D.input.values i : ℤ)) (permuteSubset e (D.mixers j)) := by
  simp only [run, Vector.getElem_map, Vector.getElem_ofFn,
    CompressionDomains.domain_value v e hv]
  exact MixerHalfLists.count_source _ _

theorem work (D : RepresentationData n) (hn : 10000 ≤ n) (v : Vector (Fin n) n)
    (e : Equiv.Perm (Fin n)) (hv : ∀ i : Fin n, v[i.val] = e i) :
    (run D v).2 ≤ inputScale D.input ^ 5 * 2 ^ mixerSize n := by
  let u := inputScale D.input
  have hu : n + 1 ≤ u := by dsimp [u, inputScale]; omega
  have hu0 : 10000 ≤ u := by omega
  have hm : mixerSize n ≤ n := by unfold mixerSize; omega
  have hl (i : Fin 3) : (CompressionDomains.domain v (D.mixers i)).1.length = mixerSize n := by
    rw [CompressionDomains.domain_value v e hv, Finset.length_sort, permuteSubset_card, D.card]
  have hcount (i : Fin 3) :
      (MixerHalfLists.count (fun j => (D.input.values j : ℤ))
        (CompressionDomains.domain v (D.mixers i)).1).2 ≤ u ^ 4 * 2 ^ mixerSize n := by
    have h := MixerHalfLists.count_scale D.input hn (fun j => (D.input.values j : ℤ))
      (CompressionDomains.domain v (D.mixers i)).1 (by rw [hl]; exact hm)
    simpa only [hl] using h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    Nat.add_le_add (CompressionDomains.domain_work v (D.mixers i)) (hcount i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hu2 : 1 ≤ u ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h24 : u ^ 2 ≤ u ^ 4 := pow_le_pow_right' (by omega) (by decide)
  have hnu2 := Nat.pow_le_pow_left hu 2
  have hT : 1 ≤ 2 ^ mixerSize n := Nat.one_le_two_pow
  have hpoly : 3 * (40 * (n + 1) ^ 2 + u ^ 4) + 12 ≤ 150 * u ^ 4 := by omega
  have hf : 150 * u ^ 4 ≤ u ^ 5 := by
    calc
      _ ≤ u * u ^ 4 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hfT := Nat.mul_le_mul_right (2 ^ mixerSize n) hf
  have hbase := Nat.mul_le_mul_right (2 ^ mixerSize n) hpoly
  change (∑ i : Fin 3, ((CompressionDomains.domain v (D.mixers i)).2 +
    (MixerHalfLists.count (fun j => (D.input.values j : ℤ))
      (CompressionDomains.domain v (D.mixers i)).1).2)) + 12 ≤ _
  change _ ≤ u ^ 5 * 2 ^ mixerSize n
  nlinarith only [hsum, hT, hbase, hfT]

end LowSpaceSubsetSum.RepresentationMixerPreparation

end OAI
