import OAI.Combinatorics.LowSpaceSubsetSum.Storage.IntervalDomainExecution

namespace OAI

/-! # The sorted outside domain from the remaining canonical interval -/

noncomputable section
namespace LowSpaceSubsetSum.CanonicalBackground

variable {n : ℕ}

private theorem in_three_intervals (m x : ℕ) :
    (∃ j : Fin 3, j.val * m ≤ x ∧ x < j.val * m + m) ↔ x < 3 * m := by
  constructor
  · rintro ⟨j, hj⟩
    fin_cases j <;> (have h := hj.2; norm_num at h; nlinarith only [h])
  · intro h
    by_cases h0 : x < m
    · exact ⟨0, by simp; omega⟩
    · by_cases h1 : x < 2 * m
      · exact ⟨1, by simp; omega⟩
      · exact ⟨2, by simp; omega⟩

theorem raw_mem (I : Instance n) (e : Equiv.Perm (Fin n)) (signs : Finset (Fin n))
    (j : Fin 3) (x : Fin n) :
    x ∈ (canonicalRepresentationData I).zeroSetup.rawMixers (e, signs) j ↔
      j.val * mixerSize n ≤ (e.symm x).val ∧
      (e.symm x).val < j.val * mixerSize n + mixerSize n := by
  change x ∈ permuteSubset e (indexInterval n (j.val * mixerSize n) (mixerSize n)) ↔ _
  simp only [permuteSubset, Finset.mem_map, indexInterval, Finset.mem_filter,
    Finset.mem_univ, true_and, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa only [Equiv.symm_apply_apply] using ha
  · intro hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩

theorem union_mem (I : Instance n) (e : Equiv.Perm (Fin n)) (signs : Finset (Fin n))
    (x : Fin n) :
    x ∈ (canonicalRepresentationData I).zeroSetup.mixerUnion (e, signs) ↔
      (e.symm x).val < 3 * mixerSize n := by
  let R := (canonicalRepresentationData I).zeroSetup
  have hordered : x ∈ R.mixerUnion (e, signs) ↔
      ∃ j : Fin 3, x ∈ R.orderedMixers (e, signs) j := by
    simp [RepresentationSetup.mixerUnion, Fin.exists_fin_succ]
  have hraw : (∃ j : Fin 3, x ∈ R.orderedMixers (e, signs) j) ↔
      ∃ j : Fin 3, x ∈ R.rawMixers (e, signs) j := by
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨R.mixerOrder (e, signs) j, hj⟩
    · rintro ⟨j, hj⟩
      refine ⟨(R.mixerOrder (e, signs)).symm j, ?_⟩
      simpa only [RepresentationSetup.orderedMixers, Equiv.apply_symm_apply] using hj
  rw [hordered, hraw]
  change (∃ j : Fin 3, x ∈ (canonicalRepresentationData I).zeroSetup.rawMixers (e, signs) j) ↔ _
  simp_rw [raw_mem]
  exact in_three_intervals _ _

def run (v : Vector (Fin n) n) : List (Fin n) × ℕ :=
  IntervalDomainExecution.run v (3 * mixerSize n) (n - 3 * mixerSize n)

theorem domain_eq (I : Instance n) (e : Equiv.Perm (Fin n)) (signs : Finset (Fin n)) :
    permuteSubset e (indexInterval n (3 * mixerSize n) (n - 3 * mixerSize n)) =
      Finset.univ \ (canonicalRepresentationData I).zeroSetup.mixerUnion (e, signs) := by
  have hm : 3 * mixerSize n ≤ n := by unfold mixerSize; omega
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, union_mem]
  simp only [permuteSubset, Finset.mem_map, indexInterval, Finset.mem_filter,
    Finset.mem_univ, true_and, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa only [Equiv.symm_apply_apply] using (show ¬ a.val < 3 * mixerSize n by omega)
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    have hb := (e.symm x).isLt
    omega

theorem value (I : Instance n) (v : Vector (Fin n) n) (e : Equiv.Perm (Fin n))
    (hv : ∀ i : Fin n, v[i.val] = e i) (signs : Finset (Fin n)) :
    (run v).1 =
      (Finset.univ \ (canonicalRepresentationData I).zeroSetup.mixerUnion (e, signs)).sort (· ≤ ·) := by
  rw [run, IntervalDomainExecution.source, CompressionDomains.domain_value v e hv,
    domain_eq I e signs]

theorem work (v : Vector (Fin n) n) : (run v).2 ≤ 40 * (n + 1) ^ 2 :=
  IntervalDomainExecution.work v _ _

theorem length_le (v : Vector (Fin n) n) : (run v).1.length ≤ n := by
  rw [run, IntervalDomainExecution.source]
  change ((MeasuredSort.sort (fun x y : Fin n => (decide (x ≤ y), 1))
    (CompressionDomains.unsorted v (indexInterval n (3 * mixerSize n)
      (n - 3 * mixerSize n)))).1).length ≤ n
  rw [MeasuredSort.sort_value, List.Perm.length_eq (List.mergeSort_perm _ _)]
  simpa only [CompressionDomains.unsorted, List.length_map] using
    CompressionDomains.positions_length (indexInterval n (3 * mixerSize n) (n - 3 * mixerSize n))

end LowSpaceSubsetSum.CanonicalBackground

end

end OAI
