import OAI.Combinatorics.LowSpaceSubsetSum.Compression.BudgetedCompressionSchedule
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionPassLedger

namespace OAI

/-! # Paying for every compression reader initialization

The arrays have nonempty factors, so their lengths are bounded by the
corresponding stream lengths. The stream-regeneration exponent margins therefore also bound
initialization at every residue.
-/

namespace LowSpaceSubsetSum.CompressionData

open scoped BigOperators
variable {n : ℕ} (D : CompressionData n)

theorem stored_lengths_positive (e : Equiv.Perm (Fin n)) (i : Fin 4) :
    0 < (D.storedFirst e i).length ∧ 0 < (D.storedSecond e i).length := by
  have hc (j : Fin 7) : 0 < (compactWeightList D.weights (D.block e j)).length := by
    rw [compactWeightList_length]
    exact Finset.card_pos.mpr ⟨0, zero_mem_distinctSums _ _⟩
  have hl : 0 < (rawWeightList D.weights (D.leftRaw e)).length := by
    rw [rawWeightList_length]
    positivity
  have hr (j : Fin 2) : 0 < (rawWeightList D.weights (D.rightRaw e j)).length := by
    rw [rawWeightList_length]
    positivity
  fin_cases i
  · exact ⟨hc 4, hc 5⟩
  · exact ⟨hc 6, hl⟩
  · refine ⟨hc 0, ?_⟩
    change 0 < (pairSumList (compactWeightList D.weights (D.block e 1))
      (rawWeightList D.weights (D.rightRaw e 0))).length
    rw [pairSumList_length]
    exact Nat.mul_pos (hc 1) (hr 0)
  · refine ⟨hc 2, ?_⟩
    change 0 < (pairSumList (compactWeightList D.weights (D.block e 3))
      (rawWeightList D.weights (D.rightRaw e 1))).length
    rw [pairSumList_length]
    exact Nat.mul_pos (hc 3) (hr 1)

theorem preparation_size_le (e : Equiv.Perm (Fin n)) :
    PreparedCompressionPass.size (PreparedCompressionPass.source D e) ≤
      2 * (∑ i : Fin 4, D.streamLength e i) + 1 := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => show
      (D.storedFirst e i).length + (D.storedSecond e i).length ≤ 2 * D.streamLength e i from by
    have hp := D.stored_lengths_positive e i
    have h₁ := Nat.le_mul_of_pos_right (D.storedFirst e i).length hp.2
    have h₂ := Nat.le_mul_of_pos_left (D.storedSecond e i).length hp.1
    unfold streamLength
    omega)
  simpa only [PreparedCompressionPass.size, PreparedCompressionPass.source,
    List.size_toArray, ← Finset.mul_sum] using Nat.add_le_add_right hs 1

private theorem half_power_ceiling (n : ℕ) :
    (2 : ℝ) ^ ((n : ℝ) / 2) ≤ ((2 ^ ((n + 1) / 2) : ℕ) : ℝ) := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hh : (n : ℝ) ≤ 2 * (((n + 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 2 * ((n + 1) / 2) by omega)
  linarith

theorem preparation_regeneration_bound (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (he : D.compactTests e = true) (hn : 10000 ≤ n) :
    q.val * PreparedCompressionPass.size (PreparedCompressionPass.source D e) ≤
      9 * 2 ^ ((n + 1) / 2) := by
  have hi (i : Fin 4) : q.val * D.streamLength e i ≤ 2 ^ ((n + 1) / 2) := by
    exact_mod_cast (D.prime_regeneration_bound e he (by omega) q i).trans (half_power_ceiling n)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => hi i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    ← Finset.mul_sum] at hs
  have hq : q.val ≤ 2 ^ ((n + 1) / 2) := by
    apply (Nat.le_of_mem_primesLE (Finset.mem_filter.mp q.property).1).trans
    apply Nat.pow_le_pow_right (by decide)
    unfold compressionPrimeExponent
    omega
  have ha := Nat.mul_le_mul_left q.val (D.preparation_size_le e)
  nlinarith only [ha, hs, hq]

theorem preparedSchedule_allowance (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (he : D.compactTests e = true) (hn : 10000 ≤ n) :
    BudgetedCompressionSchedule.allowance D.input (compressionDictionaryCapacity n) B
      (PreparedCompressionPass.source D e) q.val (primeRange_prime q.property).pos ≤
        inputScale D.input ^ 7 * 2 ^ ((n + 1) / 2) := by
  rw [BudgetedCompressionSchedule.allowance_eq]
  simp only [BudgetedPreparedCompressionPass.allowance, PreparedCompressionPass.source_value,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hp := D.preparation_regeneration_bound e q he hn
  have hj := D.sum_pass_allowance_scale B e q he hn
  have hq : q.val ≤ 2 ^ ((n + 1) / 2) := by
    apply (Nat.le_of_mem_primesLE (Finset.mem_filter.mp q.property).1).trans
    apply Nat.pow_le_pow_right (by decide)
    unfold compressionPrimeExponent
    omega
  have ht : 1 ≤ 2 ^ ((n + 1) / 2) := Nat.one_le_two_pow
  have hu : 10000 ≤ inputScale D.input := by unfold inputScale; omega
  have hu6 : 1 ≤ inputScale D.input ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hm : 20 * inputScale D.input ^ 6 ≤ inputScale D.input ^ 7 := by
    calc
      _ ≤ inputScale D.input * inputScale D.input ^ 6 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hprep := Nat.mul_le_mul_left (inputScale D.input ^ 6) hp
  have hfinal := Nat.mul_le_mul_right (2 ^ ((n + 1) / 2)) hm
  have hsmall := Nat.mul_le_mul_right (2 ^ ((n + 1) / 2)) hu6
  unfold BudgetedPreparedCompressionPass.charge
  nlinarith only [hj, hprep, hfinal, hq, ht, hsmall]

end LowSpaceSubsetSum.CompressionData

end OAI
