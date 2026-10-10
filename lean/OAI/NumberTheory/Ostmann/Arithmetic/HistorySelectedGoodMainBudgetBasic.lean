import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantFrequencyCount
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPairDerivativeBoundsAmplitude

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySelectedGoodMainBudget
open Construction Conclusion Filter HistoryProductWindows
open HistorySelectedPairDerivativeBounds HistorySelectedPairDerivativeCounts
open HistoryGiantFrequencyCount

def correctedAmplitude (Bs L : ℝ) (k l : ℕ) : ℝ :=
  Real.exp ((nominalInheritedWidth k l+2)+nominalRemovedWidth k l)*
    Real.exp (-((2^l:ℕ):ℝ)*initialGap Bs k L+sourceXiConstant l k (2+2*(k:ℝ)))

def goodMainPrefactor (Bs BD Bz L : ℝ) (k l : ℕ) : ℝ :=
  64 * correctedAmplitude Bs L k l *
    (2:ℝ)^(2^l*(2*(bulkSize k L/2))) *
    Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)) *
    Real.exp (actualFrequencyCost Bs BD Bz k*L)

def goodMainCost (Bs BD Bz : ℝ) (k : ℕ) : ℝ :=
  64 + (widthConstant k+amplitudeConstant k (2+2*(k:ℝ))) +
    3*(2:ℝ)^k + 2*actualFrequencyCost Bs BD Bz k

theorem goodMainPrefactor_nonneg (Bs BD Bz L : ℝ) (k l : ℕ) :
    0 ≤ goodMainPrefactor Bs BD Bz L k l := by
  unfold goodMainPrefactor correctedAmplitude
  positivity

theorem correctedAmplitude_le (Bs L : ℝ) {k l : ℕ} (hBs : 0 ≤ Bs)
    (hk : 0 < k) (hl : l ≤ k) :
    correctedAmplitude Bs L k l ≤
      Real.exp (widthConstant k+amplitudeConstant k (2+2*(k:ℝ))) := by
  unfold correctedAmplitude
  rw [Real.exp_add (widthConstant k)]
  apply mul_le_mul
  · exact Real.exp_le_exp.mpr (counterpartWidths_le hl)
  · exact source_amplitude_le hl (initialGap_nonneg Bs hBs hk L)
  · positivity
  · positivity

theorem bulkDensity_le {k l : ℕ} (L : ℝ) (hl : l ≤ k) :
    (2:ℝ)^(2^l*(2*(bulkSize k L/2))) ≤
      Real.exp ((2:ℝ)^k*(bulkSize k L:ℝ)) := by
  have htwo : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have he : (2^l*(2*(bulkSize k L/2)):ℕ) ≤ 2^k*bulkSize k L := by
    apply Nat.mul_le_mul (Nat.pow_le_pow_right (by omega : 1 ≤ (2:ℕ)) hl)
    omega
  calc
    _ ≤ (Real.exp 1)^(2^l*(2*(bulkSize k L/2))) :=
      pow_le_pow_left₀ (by norm_num) htwo _
    _ = Real.exp ((2^l*(2*(bulkSize k L/2)):ℕ):ℝ) := by
      rw [← Real.exp_nat_mul]
      simp
    _ ≤ _ := Real.exp_le_exp.mpr (by exact_mod_cast he)

theorem goodMainPrefactor_le (Bs BD Bz L : ℝ) {k l : ℕ}
    (hBs : 0 ≤ Bs) (hk : 0 < k) (hl : l ≤ k)
    (hm : 1 ≤ (bulkSize k L:ℝ)) (hLm : L ≤ 2*(bulkSize k L:ℝ)) :
    goodMainPrefactor Bs BD Bz L k l ≤
      Real.exp (goodMainCost Bs BD Bz k*(bulkSize k L:ℝ)) := by
  let m : ℝ := bulkSize k L
  let A := widthConstant k+amplitudeConstant k (2+2*(k:ℝ))
  have hA : 0 ≤ A := by
    dsimp only [A, widthConstant]
    positivity [amplitudeConstant_nonneg k (2+2*(k:ℝ))]
  have h64 : (64:ℝ) ≤ Real.exp (64*m) := by
    have ht := Real.add_one_le_exp (64*m)
    dsimp only [m] at ht ⊢
    linarith
  have ha : correctedAmplitude Bs L k l ≤ Real.exp (A*m) :=
    (correctedAmplitude_le Bs L hBs hk hl).trans
      (Real.exp_le_exp.mpr (le_mul_of_one_le_right hA hm))
  have hc : Real.exp (2*(2:ℝ)^l*m) ≤ Real.exp (2*(2:ℝ)^k*m) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hl)
        (by norm_num : (0:ℝ) ≤ 2)) (by dsimp only [m]; positivity)
  have hf : Real.exp (actualFrequencyCost Bs BD Bz k*L) ≤
      Real.exp (2*actualFrequencyCost Bs BD Bz k*m) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hLm (actualFrequencyCost_pos Bs BD Bz hk).le
    dsimp only [m]
    nlinarith
  calc
    _ ≤ Real.exp (64*m)*Real.exp (A*m)*Real.exp ((2:ℝ)^k*m)*
        Real.exp (2*(2:ℝ)^k*m)*Real.exp (2*actualFrequencyCost Bs BD Bz k*m) := by
      unfold goodMainPrefactor
      have hap : 0 ≤ correctedAmplitude Bs L k l := by
        unfold correctedAmplitude
        positivity
      exact mul_le_mul
        (mul_le_mul
          (mul_le_mul (mul_le_mul h64 ha hap (Real.exp_nonneg _))
            (bulkDensity_le L hl) (by positivity) (by positivity))
          hc (Real.exp_nonneg _) (by positivity))
        hf (Real.exp_nonneg _) (by positivity)
    _ = _ := by
      simp only [← Real.exp_add]
      congr 1
      dsimp only [goodMainCost, A, m]
      ring

theorem eventually_goodMainPrefactor_le (Bs BD Bz : ℝ) {k : ℕ}
    (hBs : 0 ≤ Bs) (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ l : ℕ, l ≤ k →
      goodMainPrefactor Bs BD Bz L k l ≤
        Real.exp (goodMainCost Bs BD Bz k*(bulkSize k L:ℝ)) := by
  filter_upwards [(bulkSize_tendsto_atTop hk).eventually_ge_atTop 2,
    eventually_ge_atTop (0:ℝ)] with L hm hL
  have hz : (1:ℝ) ≤ bulkScale k := by
    have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk
    simpa only [bulkScale, one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hkr 4
  have hsize := (bulkSize_bounds k hL).1
  have hLz := mul_le_mul_of_nonneg_right hz hL
  have hLm : L ≤ 2*(bulkSize k L:ℝ) := by nlinarith
  intro l hl
  exact goodMainPrefactor_le Bs BD Bz L hBs hk hl (by linarith) hLm

end Ostmann.Arithmetic.HistorySelectedGoodMainBudget

end

end OAI
