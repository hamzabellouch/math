import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PermutationSampling
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.DeficiencyVariance
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Representatives

namespace OAI

/-!
# The compressed-block trial's high-deficiency partition event

The sample space is the actual uniform permutation of input indices. Each of
the seven blocks is marginally uniform; independence between blocks is never
assumed. The floor in the retained block-list capacity is included.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem permutation_deficiency_tail (a : ι → ℤ) (K : Finset ι)
    {t : ℝ} (ht : 0 < t) :
    finiteUniformProbability (fun e : Equiv.Perm ι =>
      t ≤ |deficiency a (permuteSubset e K) - meanDeficiency a Finset.univ K.card|) ≤
        (K.card : ℝ) / t ^ 2 := by
  classical
  rw [permutationBlock_uniform_ratio K
    (fun V => t ≤ |deficiency a V - meanDeficiency a Finset.univ K.card|)]
  exact deficiency_tail_fraction_le a Finset.univ K.card (Finset.card_le_univ K) ht

/-- Exact seven-block union bound in the high-mean case. -/
theorem compression_partition_good_probability {n s : ℕ} (hn : 0 < n)
    (hs : (s : ℝ) ≤ (3 / 25 : ℝ) * n)
    (a : Fin n → ℤ) (K : Fin 7 → Finset (Fin n)) (hK : ∀ i, (K i).card = s)
    (hmean : (153 / 20000 : ℝ) * n ≤ meanDeficiency a Finset.univ s) :
    1 - (84000000 : ℝ) / n ≤ finiteUniformProbability (fun e : Equiv.Perm (Fin n) =>
      ∀ i, (151 / 20000 : ℝ) * n ≤ deficiency a (permuteSubset e (K i))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : (0 : ℝ) < (n : ℝ) / 10000 := by positivity
  have hbad (i : Fin 7) : finiteUniformProbability (fun e : Equiv.Perm (Fin n) =>
      deficiency a (permuteSubset e (K i)) < (151 / 20000 : ℝ) * n) ≤
        (12000000 : ℝ) / n := by
    have hinc : ∀ e : Equiv.Perm (Fin n),
        deficiency a (permuteSubset e (K i)) < (151 / 20000 : ℝ) * n →
        (n : ℝ) / 10000 ≤
          |deficiency a (permuteSubset e (K i)) - meanDeficiency a Finset.univ s| := by
      intro e he
      have habs := neg_le_abs
        (deficiency a (permuteSubset e (K i)) - meanDeficiency a Finset.univ s)
      linarith
    apply (finiteUniformProbability_mono hinc).trans
    have htail := permutation_deficiency_tail a (K i) ht
    rw [hK i] at htail
    apply htail.trans
    calc
      (s : ℝ) / ((n : ℝ) / 10000) ^ 2 ≤
          ((3 / 25 : ℝ) * n) / ((n : ℝ) / 10000) ^ 2 :=
        div_le_div_of_nonneg_right hs (sq_nonneg _)
      _ = (12000000 : ℝ) / n := by field_simp; ring
  have hunion := (finiteUniformProbability_exists_le_sum
    (fun (i : Fin 7) (e : Equiv.Perm (Fin n)) =>
      deficiency a (permuteSubset e (K i)) < (151 / 20000 : ℝ) * n)).trans
        (Finset.sum_le_sum (fun i _ => hbad i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hunion
  have hunion' : finiteUniformProbability (fun e : Equiv.Perm (Fin n) =>
      ∃ i, deficiency a (permuteSubset e (K i)) < (151 / 20000 : ℝ) * n) ≤
        (84000000 : ℝ) / n := by
    convert hunion using 1
    norm_num
    ring
  have hcompl : (fun e : Equiv.Perm (Fin n) =>
      ∀ i, (151 / 20000 : ℝ) * n ≤ deficiency a (permuteSubset e (K i))) =
      (fun e => ¬∃ i, deficiency a (permuteSubset e (K i)) < (151 / 20000 : ℝ) * n) := by
    ext e
    simp
  rw [hcompl, finiteUniformProbability_compl]
  linarith

noncomputable def compressionCapExponent (n : ℕ) : ℕ :=
  ⌊((mixerSize n / 2 : ℕ) : ℝ) - (3 / 400 : ℝ) * n⌋₊

theorem compression_block_size_test {n : ℕ} (hn : 20000 ≤ n)
    (a : Fin n → ℤ) (V : Finset (Fin n)) (hV : V.card = mixerSize n / 2)
    (hd : (151 / 20000 : ℝ) * n ≤ deficiency a V) :
    distinctSumCount a V ≤ 2 ^ compressionCapExponent n := by
  have hnR : (20000 : ℝ) ≤ n := by exact_mod_cast hn
  have hfloor := Nat.lt_floor_add_one
    (((mixerSize n / 2 : ℕ) : ℝ) - (3 / 400 : ℝ) * n)
  have hexp : (V.card : ℝ) - deficiency a V ≤ (compressionCapExponent n : ℝ) := by
    simp only [compressionCapExponent, hV]
    linarith
  have hcount : (distinctSumCount a V : ℝ) ≤ (2 : ℝ) ^ compressionCapExponent n := by
    rw [← two_pow_card_sub_deficiency a V]
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hexp
  exact_mod_cast hcount

/-- The actual seven size tests pass with probability at least one half for
an absolute explicit threshold. This is only the partition event, before
prime sampling and the solution-bucket argument. -/
theorem compression_size_tests_probability {n : ℕ} (hn : 168000000 ≤ n)
    (a : Fin n → ℤ) (K : Fin 7 → Finset (Fin n))
    (hK : ∀ i, (K i).card = mixerSize n / 2)
    (hmean : (153 / 20000 : ℝ) * n ≤
      meanDeficiency a Finset.univ (mixerSize n / 2)) :
    (1 / 2 : ℝ) ≤ finiteUniformProbability (fun e : Equiv.Perm (Fin n) =>
      ∀ i, distinctSumCount a (permuteSubset e (K i)) ≤ 2 ^ compressionCapExponent n) := by
  have hs : ((mixerSize n / 2 : ℕ) : ℝ) ≤ (3 / 25 : ℝ) * n := by
    have hdiv : mixerSize n = 2 * (mixerSize n / 2) := by
      simp only [mixerSize]
      omega
    have hu := (mixerSize_bounds n).2
    rw [hdiv, Nat.cast_mul, Nat.cast_ofNat] at hu
    linarith
  have hgood := compression_partition_good_probability (by omega : 0 < n)
    hs a K hK hmean
  have hnR : (168000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hhalf : (1 / 2 : ℝ) ≤ 1 - (84000000 : ℝ) / n := by
    have hd : (84000000 : ℝ) / n ≤ 1 / 2 := by
      apply (div_le_iff₀ (by linarith : (0 : ℝ) < n)).mpr
      linarith
    linarith
  apply (hhalf.trans hgood).trans
  apply finiteUniformProbability_mono
  intro e he i
  exact compression_block_size_test (by omega) a (permuteSubset e (K i))
    (by rw [permuteSubset_card, hK i]) (he i)

end LowSpaceSubsetSum

end OAI
