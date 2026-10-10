import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightExponential

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedPairDerivativeBounds
open Construction Characters.RationalHistory HistoryOccurrenceVariables HistoryPairSmoothXi
open HistorySymbolicEncoding HistoryProductWindows

def amplitudeConstant (k : ℕ) (E : ℝ) : ℝ :=
  (2:ℝ)^k * |E+12+4*(k:ℝ)+2*Real.log leafFourierBound|

lemma amplitudeConstant_nonneg (k : ℕ) (E : ℝ) : 0 ≤ amplitudeConstant k E := by
  unfold amplitudeConstant
  positivity

theorem source_amplitude_le {l k : ℕ} (hl : l ≤ k) {Δ E : ℝ} (hΔ : 0 ≤ Δ) :
    Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k E) ≤
      Real.exp (amplitudeConstant k E) := by
  apply Real.exp_le_exp.mpr
  have hp : (2:ℝ)^l ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hl
  have hgap : 0 ≤ ((2^l:ℕ):ℝ)*Δ := mul_nonneg (Nat.cast_nonneg _) hΔ
  have hc := mul_le_mul_of_nonneg_left
    (le_abs_self (E+12+4*(k:ℝ)+2*Real.log leafFourierBound)) (pow_nonneg (by norm_num : (0:ℝ)≤2) l)
  have hc' := mul_le_mul_of_nonneg_right hp
    (abs_nonneg (E+12+4*(k:ℝ)+2*Real.log leafFourierBound))
  simp only [sourceXiConstant, Nat.cast_pow, Nat.cast_ofNat] at *
  dsimp only [amplitudeConstant]
  linarith

theorem add_exp_bounds {a b A B m : ℝ} (hm : 1 ≤ m) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : a ≤ Real.exp (A*m)) (hb : b ≤ Real.exp (B*m)) :
    a+b ≤ Real.exp ((A+B+1)*m) := by
  have hm0 : 0 ≤ m := by linarith
  have ha' := ha.trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (by linarith : A ≤ A+B) hm0))
  have hb' := hb.trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (by linarith : B ≤ A+B) hm0))
  have ht : 2 ≤ Real.exp m := (by linarith : (2:ℝ) ≤ m+1).trans (Real.add_one_le_exp m)
  calc
    a+b ≤ 2*Real.exp ((A+B)*m) := by linarith
    _ ≤ Real.exp m*Real.exp ((A+B)*m) :=
      mul_le_mul_of_nonneg_right ht (Real.exp_nonneg _)
    _ = Real.exp ((A+B+1)*m) := by rw [← Real.exp_add]; congr 1; ring

theorem source_derivative_core_le {b k l : ℕ} {V : ℕ → ℕ} {tb Δ E CK m : ℝ}
    (center : ℕ → ℝ) (hl : l ≤ k) (hΔ : 0 ≤ Δ) (hCK : 0 ≤ CK)
    (hm : 1 ≤ m) (hb : (b:ℝ) ≤ m)
    (hK : sourceCancellationBound V b k tb center l ≤ Real.exp (CK*m)) :
    Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k E)*historyDerivativeCount l*
      actualSourceDerivativeRate (sourceHistoryBudget V b k l tb center) ≤
      Real.exp ((|Real.log (sourceDerivativePrefactor k E)|+1+CK*(k:ℝ))*m) := by
  have ht := source_pair_derivative_budget_le b k l Δ E
    (sourceCancellationBound V b k tb center l) CK m hl hΔ
    (sourceCancellationBound_one_le _ _ _ _ _ _) hCK hm hb hK
  rw [sourceLeafAmplitude_pair] at ht
  have hpos : 0 ≤ Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k E)*
      historyDerivativeCount l*actualSourceDerivativeRate (sourceHistoryBudget V b k l tb center) :=
    mul_nonneg (mul_nonneg (Real.exp_nonneg _) (historyDerivativeCount_nonneg l))
      (actualSourceDerivativeRate_nonneg (sourceHistoryBudget_nonneg _ _ _ _ _ _))
  have he := linear_prefactor_mul_exp_le (sourceDerivativePrefactor k E) (CK*(k:ℝ)) m
    (sourceDerivativePrefactor_pos k E) (mul_nonneg hCK (Nat.cast_nonneg _)) hm
  change 2*_*_*actualSourceDerivativeRate (sourceHistoryBudget V b k l tb center) ≤ _ at ht
  nlinarith

end Ostmann.Arithmetic.HistorySelectedPairDerivativeBounds

end

end OAI
