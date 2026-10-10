import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateNormalizationActual
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateTotalCount
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsTargets

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate HistoryFrequencyBudget
open HistoryFrequencyLabels InitialCharacterScale Filter
attribute [local instance] Classical.propDecidable

theorem gapSchedule_nonneg_of_nonneg {BD : ℝ} (hBD : 0 ≤ BD)
    (k : ℕ) (L : ℝ) (j : ℕ) : 0 ≤ gapSchedule BD k L j := by
  have hb : 0 ≤ BD+20*Real.log (depthScale k) :=
    add_nonneg hBD (mul_nonneg (by norm_num) (Real.log_nonneg (one_le_depthScale k)))
  have hi : 0 ≤ initialGap BD k L :=
    mul_nonneg hb (Nat.cast_nonneg _)
  cases j with
  | zero => exact hi
  | succ j => simp only [gapSchedule]; positivity

def changingNormalizationCoefficient (k : ℕ) (ρ c₀ : ℝ) : ℝ :=
  (|Real.log ρ|+2)*(2:ℝ)^k*depthScale k+(2^k:ℕ)*|Real.log c₀|

theorem changingNormalizationCoefficient_nonneg (k : ℕ) (ρ c₀ : ℝ) :
    0 ≤ changingNormalizationCoefficient k ρ c₀ := by
  unfold changingNormalizationCoefficient
  have hz := (depthScale_pos k).le
  positivity

theorem normalization_power_le_exp_quadratic (k : ℕ) (ρ c₀ : ℝ)
    {L : ℝ} (hL : 1 ≤ L) {j : ℕ} (hj : j ≤ k) :
    L ^ (-((2^j*wordSize k L:ℕ):ℝ)) * Real.exp
      ((|Real.log ρ|+2)*((2^j*wordSize k L:ℕ):ℝ)+(2^k:ℕ)*|Real.log c₀|) ≤
    Real.exp (changingNormalizationCoefficient k ρ c₀*L^2) := by
  have hpow : L ^ (-((2^j*wordSize k L:ℕ):ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hz := (depthScale_pos k).le
  have hm := (wordSize_bounds k (by linarith : 0 ≤ L)).2
  have hp : (2:ℝ)^j ≤ 2^k := pow_le_pow_right₀ (by norm_num) hj
  have hmul : ((2^j*wordSize k L:ℕ):ℝ) ≤ (2:ℝ)^k*depthScale k*L := by
    push_cast
    exact (mul_le_mul hp hm (Nat.cast_nonneg _) (by positivity)).trans_eq (by ring)
  have ha : 0 ≤ |Real.log ρ|+2 := by positivity
  have hb : 0 ≤ (2^k:ℕ)*|Real.log c₀| := by positivity
  have hc : 0 ≤ (|Real.log ρ|+2)*(2:ℝ)^k*depthScale k := by positivity
  have hLs : L ≤ L^2 := by nlinarith
  have h1s : 1 ≤ L^2 := by nlinarith
  calc
    _ ≤ 1*Real.exp ((|Real.log ρ|+2)*((2^j*wordSize k L:ℕ):ℝ)+
        (2^k:ℕ)*|Real.log c₀|) := mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ ≤ _ := by
      rw [one_mul]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hmul ha
      have hl := mul_le_mul_of_nonneg_left hLs hc
      have hq := mul_le_mul_of_nonneg_left h1s hb
      unfold changingNormalizationCoefficient
      nlinarith

theorem changing_scalar_budget {C N H A B W G L : ℝ}
    (hL : 1 ≤ L) (hW : 0 ≤ W) (hG : 0 ≤ G)
    (hN : 0 ≤ N) (hH : 0 ≤ H)
    (hC : C ≤ Real.exp (A*L^2))
    (hcount : N*H ≤ Real.exp (B*L^2)) :
    C*Real.exp (-G+W)*N*H ≤ Real.exp ((A+W+B)*L^2) := by
  have h1 : 1 ≤ L^2 := by nlinarith
  have hg : Real.exp (-G+W) ≤ Real.exp (W*L^2) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left h1 hW
    linarith
  have hc := mul_le_mul hC hg (Real.exp_pos _).le (Real.exp_pos _).le
  have hh := mul_le_mul hc hcount (mul_nonneg hN hH)
    (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  calc
    _ = (C*Real.exp (-G+W))*(N*H) := by ring
    _ ≤ _ := hh
    _ = _ := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring

end Ostmann.Characters.DiagonalEstimate

end

end OAI
