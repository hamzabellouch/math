import OAI.NumberTheory.TwoPoint.Walks.WitnessSystemCodes
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-! The concrete witness relation records have polynomial cost per witness. -/

namespace TwoPointCorrelations

lemma card_witnessSystemData_exp (n N : ℕ) (ι : Type*) [Fintype ι]
    (hlabels : Fintype.card ι ≤ N + 1) (hn : n ≤ N + 1) :
    (Fintype.card (WitnessSystemData n N ι) : ℝ) ≤
      Real.exp (Real.log 4 + (n : ℝ) * (Real.log 2 + 7 * Real.log (N + 1))) := by
  have hpoly : Fintype.card ι ^ 2 * n * (N + 1) ^ 4 ≤ (N + 1) ^ 7 := by
    calc
      _ ≤ (N + 1) ^ 2 * (N + 1) * (N + 1) ^ 4 := by gcongr
      _ = _ := by ring
  have h1 : 1 ≤ (N + 1) ^ 7 := one_le_pow₀ (by omega)
  have hcount := card_witnessSystemData_le n N ι
  have hmajor : Fintype.card (WitnessSystemData n N ι) ≤
      4 * (2 * (N + 1) ^ 7) ^ n := by
    apply hcount.trans
    gcongr
    omega
  have hpos : (0 : ℝ) < N + 1 := by positivity
  have h7 : Real.exp (7 * Real.log ((N : ℝ) + 1)) = ((N : ℝ) + 1) ^ (7 : ℕ) := by
    simpa only [Nat.cast_ofNat, Real.exp_log hpos] using
      (Real.exp_nat_mul (Real.log ((N : ℝ) + 1)) 7)
  calc
    _ ≤ (4 : ℝ) * (2 * ((N : ℝ) + 1) ^ (7 : ℕ)) ^ n := by exact_mod_cast hmajor
    _ = _ := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4), Real.exp_nat_mul,
        Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), h7]

/-- The selected-system metadata fits within the same `exp(O(L log²L))`
allowance as the underlying word patterns. -/
theorem card_witnessSystemData_scale (n N : ℕ) (ι : Type*) [Fintype ι]
    (L : ℝ) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hlabels : Fintype.card ι ≤ N + 1) (hnN : n ≤ N + 1)
    (hn : (n : ℝ) ≤ 4 * L) (hN : (N : ℝ) + 1 ≤ L ^ (2 : ℕ)) :
    (Fintype.card (WitnessSystemData n N ι) : ℝ) ≤
      Real.exp (63 * L * (Real.log L) ^ 2) := by
  have hlog4 : Real.log 4 ≤ 3 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogN : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log L := by
    have ht := Real.log_le_log (by positivity : (0 : ℝ) < N + 1) hN
    simpa only [Real.log_pow, Nat.cast_ofNat] using ht
  have hm := mul_le_mul_of_nonneg_left
    (show Real.log 2 + 7 * Real.log ((N : ℝ) + 1) ≤ 15 * Real.log L by linarith)
    (show (0 : ℝ) ≤ n by positivity)
  have hn' := mul_le_mul_of_nonneg_right hn (show 0 ≤ 15 * Real.log L by linarith)
  have hl : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
  have hl' := mul_le_mul_of_nonneg_left hl (show 0 ≤ 60 * L by positivity)
  have hsq : 1 ≤ L * (Real.log L) ^ 2 := by nlinarith [sq_nonneg (Real.log L)]
  apply (card_witnessSystemData_exp n N ι hlabels hnN).trans
  apply Real.exp_le_exp.mpr
  nlinarith

end TwoPointCorrelations

end OAI
