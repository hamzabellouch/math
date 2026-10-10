import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyBudgetBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceBounds
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Template Construction InitialCharacterScale HistoryFrequencyBudget HistoryFrequencyLabels

def sourceFrequencyRate (BD : ℝ) (k : ℕ) : ℝ := BD+20*Real.log (depthScale k)

def sourceRecurrenceB {k : ℕ} (cfg : SourceConfiguration k) (J : ℤ)
    (gaps : ℕ → ℝ) (c : ℝ) (j : ℕ) (_ : Template.State k (j+1)) : ℤ :=
  (⌊Real.exp (sourcePivotTarget cfg J gaps j+sourceAtomWidth k c)⌋₊:ℕ)

def sourceRecurrenceV (BD : ℝ) (k : ℕ) (L : ℝ) (j : ℕ)
    (_ : Template.State k (j+1)) : ℤ :=
  bound (sourceFrequencyRate BD k) (wordSize k L:ℝ) j

theorem sourceFrequencyRate_nonneg {BD : ℝ} (hBD : 1≤BD) (k : ℕ) :
    0≤ sourceFrequencyRate BD k := by
  have hh := Real.log_nonneg (one_le_depthScale k)
  unfold sourceFrequencyRate
  linarith

theorem sourceRecurrenceB_nonneg {k : ℕ} (cfg : SourceConfiguration k) (J : ℤ)
    (gaps : ℕ → ℝ) (c : ℝ) (j : ℕ) (x : Template.State k (j+1)) :
    0≤ sourceRecurrenceB cfg J gaps c j x := Int.natCast_nonneg _

theorem sourceRecurrenceB_upper {k : ℕ} (cfg : SourceConfiguration k) (J : ℤ)
    (gaps : ℕ → ℝ) (c : ℝ) (j : ℕ) (x : Template.State k (j+1)) :
    (sourceRecurrenceB cfg J gaps c j x:ℝ)≤
      Real.exp (sourcePivotTarget cfg J gaps j+sourceAtomWidth k c) :=
  Nat.floor_le (Real.exp_pos _).le

theorem sourceRecurrenceB_pivot_le {k : ℕ} (cfg : SourceConfiguration k) (J : ℤ)
    (gaps : ℕ → ℝ) (c : ℝ) (j : ℕ) (x : Template.State k (j+1))
    {P : ℕ+} (hP : P∈sourcePivotRanges cfg J gaps c j) :
    (P:ℤ)≤ sourceRecurrenceB cfg J gaps c j x := by
  have hi : (P:ℕ)≤⌊Real.exp (sourcePivotTarget cfg J gaps j+sourceAtomWidth k c)⌋₊ :=
    (Nat.le_floor_iff (Real.exp_pos _).le).mpr (sourcePivotRanges_upper cfg J gaps c j hP)
  unfold sourceRecurrenceB
  exact_mod_cast hi

theorem sourceRecurrenceV_root_bound (BD : ℝ) (k : ℕ) (L : ℝ) (j : ℕ)
    (x : Template.State k (j+1))
    (z : SupportedHistory (ranges (sourceFrequencyRate BD k) (wordSize k L:ℝ) j) j []) :
    |z.val.1|≤ sourceRecurrenceV BD k L j x := by
  have hm := supportedHistory_root_mem z
  have hz := (mem_signedRange (bound (sourceFrequencyRate BD k) (wordSize k L:ℝ) j) z.val.1).mp
    (by simpa only [ranges,List.length_nil,Nat.sub_zero] using hm)
  rw [Int.abs_eq_natAbs]
  unfold sourceRecurrenceV
  exact_mod_cast hz.2

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
