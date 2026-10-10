import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceGaps
import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyBudgetBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsTargets

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Filter InitialCharacterScale

theorem exp_le_two_floor_exp {E : ℝ} (hE : Real.log 2 ≤ E) :
    Real.exp E ≤ 2*(⌊Real.exp E⌋₊ : ℝ) := by
  have htwo : (2 : ℝ) ≤ Real.exp E := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ)<2)] using Real.exp_le_exp.mpr hE
  have hf := Nat.lt_floor_add_one (Real.exp E)
  linarith

theorem recurrence_window_scalar (T A C E E' Δ : ℝ)
    (hfirst : Real.log 2+A+C < Δ-E)
    (hnext : Real.log 4+A+C ≤ E'-E-Δ)
    (hE' : Real.log 2 ≤ E') :
    2*(⌊Real.exp (T+A)⌋₊ : ℝ)*(⌊Real.exp E⌋₊ : ℝ) < Real.exp (T+Δ-C) ∧
    2*(⌊Real.exp E⌋₊ : ℝ)*Real.exp (T+Δ+C) ≤
      (⌊Real.exp E'⌋₊ : ℝ)*Real.exp (T-A) := by
  have hfT := Nat.floor_le (Real.exp_pos (T+A)).le
  have hfE := Nat.floor_le (Real.exp_pos E).le
  have hfE' := exp_le_two_floor_exp hE'
  constructor
  · calc
      _ ≤ 2*Real.exp (T+A)*Real.exp E :=
        mul_le_mul (mul_le_mul_of_nonneg_left hfT (by norm_num)) hfE
          (by positivity) (by positivity)
      _ = Real.exp (Real.log 2+(T+A)+E) := by
        simp only [Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ)<2)]
      _ < _ := Real.exp_lt_exp.mpr (by linarith)
  · have hexp : 4*Real.exp E*Real.exp (T+Δ+C) ≤ Real.exp E'*Real.exp (T-A) := by
      calc
        _ = Real.exp (Real.log 4+E+(T+Δ+C)) := by
          simp only [Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ)<4)]
        _ ≤ Real.exp (E'+(T-A)) := Real.exp_le_exp.mpr (by linarith)
        _ = _ := Real.exp_add _ _
    have hl := mul_le_mul_of_nonneg_right hfE (Real.exp_pos (T+Δ+C)).le
    have hu := mul_le_mul_of_nonneg_right hfE' (Real.exp_pos (T-A)).le
    nlinarith

theorem recurrence_window_reserves (BD : ℝ) (k : ℕ) (L : ℝ) (j : ℕ) :
    gapSchedule BD k L (j+1)-
      HistoryFrequencyBudget.exponent (BD+20*Real.log (depthScale k)) (wordSize k L) j =
      2*(4 : ℝ)^j*Real.sqrt (wordSize k L : ℝ) ∧
    HistoryFrequencyBudget.exponent (BD+20*Real.log (depthScale k)) (wordSize k L) (j+1)-
      HistoryFrequencyBudget.exponent (BD+20*Real.log (depthScale k)) (wordSize k L) j-
      gapSchedule BD k L (j+1) = 2*(4 : ℝ)^j*Real.sqrt (wordSize k L : ℝ) := by
  simp only [gapSchedule,initialGap,HistoryFrequencyBudget.exponent,pow_succ]
  constructor <;> ring

theorem eventually_recurrence_window_budget (BD A C : ℝ) (k : ℕ) (hBD : 1 ≤ BD) :
    ∀ᶠ L : ℝ in atTop, ∀j : ℕ, ∀T : ℝ,
      2*(⌊Real.exp (T+A)⌋₊ : ℝ)*
          (HistoryFrequencyBudget.bound (BD+20*Real.log (depthScale k)) (wordSize k L) j : ℝ) <
        Real.exp (T+gapSchedule BD k L (j+1)-C) ∧
      2*(HistoryFrequencyBudget.bound (BD+20*Real.log (depthScale k)) (wordSize k L) j : ℝ)*
          Real.exp (T+gapSchedule BD k L (j+1)+C) ≤
        (HistoryFrequencyBudget.bound (BD+20*Real.log (depthScale k)) (wordSize k L) (j+1) : ℝ)*
          Real.exp (T-A) := by
  filter_upwards [(Real.tendsto_sqrt_atTop.comp (wordSize_tendsto k)).eventually_ge_atTop
      (|A|+|C|+|Real.log 4|+|Real.log 2|+2),
    (wordSize_tendsto k).eventually_ge_atTop (Real.log 2)] with L hres hm
  simp only [Function.comp_apply] at hres
  intro j T
  have hs := Real.sqrt_nonneg (wordSize k L : ℝ)
  have h4 : (1 : ℝ) ≤ 4^j := one_le_pow₀ (by norm_num)
  have hmargin : 2*Real.sqrt (wordSize k L : ℝ) ≤
      2*(4 : ℝ)^j*Real.sqrt (wordSize k L : ℝ) := by nlinarith
  obtain ⟨he1,he2⟩ := recurrence_window_reserves BD k L j
  apply recurrence_window_scalar
  · rw [he1]
    linarith [le_abs_self A,le_abs_self C,le_abs_self (Real.log 2),abs_nonneg (Real.log 4)]
  · rw [he2]
    linarith [le_abs_self A,le_abs_self C,le_abs_self (Real.log 4),abs_nonneg (Real.log 2)]
  · have ha : 1 ≤ BD+20*Real.log (depthScale k) := by
      linarith [Real.log_nonneg (one_le_depthScale k)]
    have h2 : (1 : ℝ) ≤ 2^(j+1) := one_le_pow₀ (by norm_num)
    have hrate : 1 ≤ (2 : ℝ)^(j+1)*(BD+20*Real.log (depthScale k)) := by nlinarith
    have hx := mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg (α:=ℝ) (wordSize k L))
    have hpos : 0 ≤ 2*(4 : ℝ)^(j+1)*Real.sqrt (wordSize k L : ℝ) := by positivity
    dsimp only [HistoryFrequencyBudget.exponent]
    linarith

theorem eventually_source_recurrence_window_budget (BD c : ℝ) (k : ℕ) (hBD : 1 ≤ BD) :
    ∀ᶠ L : ℝ in atTop, ∀j : ℕ, ∀T : ℝ,
      2*(⌊Real.exp (T+sourceAtomWidth k c)⌋₊ : ℝ)*
          (HistoryFrequencyBudget.bound (BD+20*Real.log (depthScale k)) (wordSize k L) j : ℝ) <
        Real.exp (T+gapSchedule BD k L (j+1)-sourceCopiedWidth k c) ∧
      2*(HistoryFrequencyBudget.bound (BD+20*Real.log (depthScale k)) (wordSize k L) j : ℝ)*
          Real.exp (T+gapSchedule BD k L (j+1)+sourceCopiedWidth k c) ≤
        (HistoryFrequencyBudget.bound (BD+20*Real.log (depthScale k)) (wordSize k L) (j+1) : ℝ)*
          Real.exp (T-sourceAtomWidth k c) :=
  eventually_recurrence_window_budget BD (sourceAtomWidth k c) (sourceCopiedWidth k c) k hBD

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
