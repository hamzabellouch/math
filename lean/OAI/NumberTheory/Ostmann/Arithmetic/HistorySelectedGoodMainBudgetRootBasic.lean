import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedGoodMainBudgetActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedGoodMainBudget
open Construction Conclusion Filter HistoryGiantFrequencyCount

def rootGoodMainPrefactor (Bs BD Bz L : ℝ) (k l : ℕ) : ℝ :=
  64 * correctedAmplitude Bs L k l *
    (2:ℝ)^(2^l*(2*(bulkSize k L/2))) *
    Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)) *
    Real.exp (2*actualFrequencyCost Bs BD Bz k*L)

theorem rootGoodMainPrefactor_eq (Bs BD Bz L : ℝ) (k l : ℕ) :
    rootGoodMainPrefactor Bs BD Bz L k l =
      goodMainPrefactor Bs BD Bz L k l * Real.exp (actualFrequencyCost Bs BD Bz k*L) := by
  have he : Real.exp (2*actualFrequencyCost Bs BD Bz k*L) =
      Real.exp (actualFrequencyCost Bs BD Bz k*L)*Real.exp (actualFrequencyCost Bs BD Bz k*L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold rootGoodMainPrefactor goodMainPrefactor
  rw [he]
  ring

theorem eventually_extraRootFrequency_le (Bs BD Bz : ℝ) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (actualFrequencyCost Bs BD Bz k*L) ≤
        Real.exp (2*actualFrequencyCost Bs BD Bz k*(bulkSize k L:ℝ)) := by
  filter_upwards [(bulkSize_tendsto_atTop hk).eventually_ge_atTop 2,
    eventually_ge_atTop (0:ℝ)] with L hm hL
  have hz : (1:ℝ) ≤ bulkScale k := by
    have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk
    simpa only [bulkScale, one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hkr 4
  have hsize := (bulkSize_bounds k hL).1
  have hLz := mul_le_mul_of_nonneg_right hz hL
  have hLm : L ≤ 2*(bulkSize k L:ℝ) := by nlinarith
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hLm (actualFrequencyCost_pos Bs BD Bz hk).le
  nlinarith

theorem extraRootFrequency_absorb (Bs BD Bz H L : ℝ) {k l : ℕ} (hk : 0 < k)
    (hF : Real.exp (actualFrequencyCost Bs BD Bz k*L) ≤
      Real.exp (2*actualFrequencyCost Bs BD Bz k*(bulkSize k L:ℝ)))
    {D : ℝ}
    (hD : goodMainPrefactor Bs BD Bz L k l*D ≤
      Real.exp (-(H+2*actualFrequencyCost Bs BD Bz k)*(2:ℝ)^l*(bulkSize k L:ℝ))) :
    rootGoodMainPrefactor Bs BD Bz L k l*D ≤
      Real.exp (-H*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
  have hpow : (1:ℝ) ≤ (2:ℝ)^l := one_le_pow₀ (by norm_num)
  have hp := mul_nonneg (actualFrequencyCost_pos Bs BD Bz hk).le
    (Nat.cast_nonneg (bulkSize k L) (α:=ℝ))
  have hprod := mul_le_mul_of_nonneg_right hpow hp
  calc
    _ = (goodMainPrefactor Bs BD Bz L k l*D)*Real.exp (actualFrequencyCost Bs BD Bz k*L) := by
      rw [rootGoodMainPrefactor_eq]
      ring
    _ ≤ Real.exp (-(H+2*actualFrequencyCost Bs BD Bz k)*(2:ℝ)^l*(bulkSize k L:ℝ))*
        Real.exp (2*actualFrequencyCost Bs BD Bz k*(bulkSize k L:ℝ)) :=
      mul_le_mul hD hF (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith

end Ostmann.Arithmetic.HistorySelectedGoodMainBudget

end

end OAI
