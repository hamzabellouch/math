import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantCompensationErrorBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusActualSources

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantCompensationError
open Conclusion HistorySignedResidues

def compensationCost (Bs BD Bz : ℝ) (k N : ℕ) : ℝ :=
  (N:ℝ)*actualFactorConstant Bs BD Bz k*(bulkScale k+2)

theorem compensationCost_nonneg (Bs BD Bz : ℝ) (k N : ℕ) :
    0 ≤ compensationCost Bs BD Bz k N := by
  unfold compensationCost bulkScale
  have := (actualFactorConstant_pos Bs BD Bz k).le
  positivity

theorem actualFactorCap_log_le (Bs BD Bz : ℝ) (k : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    actualFactorConstant Bs BD Bz k*((bulkSize k L:ℝ)+1)+
      actualFactorConstant Bs BD Bz k*Real.exp ((1/100:ℝ)*L) ≤
      rawLogBudget (actualFactorConstant Bs BD Bz k*(bulkScale k+2)) L := by
  have hA := (actualFactorConstant_pos Bs BD Bz k).le
  have hB : 0 ≤ bulkScale k := by unfold bulkScale; positivity
  have he : 1 ≤ Real.exp ((1/100:ℝ)*L) := Real.one_le_exp (by positivity)
  have hl : L+1 ≤ (L+1)^2 := by nlinarith
  have hs : 1 ≤ (L+1)^2 := by nlinarith
  have hm : (bulkSize k L:ℝ)+1 ≤ (bulkScale k+1)*(L+1) := by
    have := (bulkSize_bounds k hL).2
    nlinarith
  have hm' := hm.trans (mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ bulkScale k+1))
  have hm'' := hm'.trans (le_mul_of_one_le_right
    (by positivity : 0 ≤ (bulkScale k+1)*(L+1)^2) he)
  have he' := mul_le_mul_of_nonneg_right hs (Real.exp_nonneg ((1/100:ℝ)*L))
  have h1 := mul_le_mul_of_nonneg_left hm'' hA
  have h2 := mul_le_mul_of_nonneg_left he' hA
  unfold rawLogBudget
  nlinarith

theorem actualFactorCap_pow_le (Bs BD Bz : ℝ) (k N : ℕ) {n : ℕ} (hn : n ≤ N)
    {L : ℝ} (hL : 0 ≤ L) :
    (actualFactorCap Bs BD Bz k L)^n ≤
      Real.exp (rawLogBudget (compensationCost Bs BD Bz k N) L) := by
  calc
    _ ≤ (actualFactorCap Bs BD Bz k L)^N :=
      pow_le_pow_right₀ (actualFactorCap_one_le Bs BD Bz k L) hn
    _ = Real.exp ((N:ℝ)*(actualFactorConstant Bs BD Bz k*((bulkSize k L:ℝ)+1)+
        actualFactorConstant Bs BD Bz k*Real.exp ((1/100:ℝ)*L))) := by
      rw [actualFactorCap,Real.exp_nat_mul]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (actualFactorCap_log_le Bs BD Bz k hL)
        (Nat.cast_nonneg N : (0:ℝ) ≤ N)
      simpa only [rawLogBudget,compensationCost,mul_assoc] using h

theorem internalCount_le (k l : ℕ) (hl : l ≤ k) : 4*l*2^l ≤ 4*k*2^k := by
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hl) (Nat.pow_le_pow_right (by omega) hl)

end Ostmann.Arithmetic.HistoryGiantCompensationError

end

end OAI
