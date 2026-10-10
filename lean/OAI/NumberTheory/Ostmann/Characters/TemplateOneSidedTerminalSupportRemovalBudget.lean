import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateFrequencyScales
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSourceHistory
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalNumerics
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationTerminalDataSource
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportSurvivingBudgetDivisors
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval
open Template SymbolicHistory TemplateOneSidedBudget TemplateOneSidedRelabel
open TemplateOneSidedSupportTelescoping TemplateOneSidedSupportSurviving
open TemplateOneSidedCancellation HigherBiasSource HigherBiasSource.SourceTemplate
open DiagonalEstimate InitialCharacterScale HistoryFrequencyLabels HistoryFrequencyBudget Filter
attribute [local instance] Classical.propDecidable

abbrev terminalFamilies (k j : ℕ) (width : Role→ℕ) (s : ℤ)
    (t : HistoryReconstruction.Tree j) :=
  actualFamilies k (fun u=>(width ((schedule k j).role u))) j
    (SampleOrigins.root k j) s (sampledExpressions k j width) t

theorem terminalFamilies_syntax (k j : ℕ) (width : Role→ℕ) (N : ℕ)
    (hw : ∀r,width r ≤ N) (s : ℤ) (t : HistoryReconstruction.Tree j)
    (i : (schedule k j).Constituent width) (e : Expr ((schedule k j).Constituent width))
    (he : e∈terminalFamilies k j width s t i) :
    e.syntaxSize ≤ 3*obstructionSizeFactor k j*(N+1) :=
  (sampled_obstructions_size k j width N hw false s t e
    (actualFamilies_obstructions _ _ _ _ _ _ _ false i e he)).1

theorem terminalFamilies_fixedLog {a m H : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m)
    (k j : ℕ) (width : Role→ℕ) (s : ℤ) (t : HistoryReconstruction.Tree j)
    (ht : RangeSupported (ranges a m j) j [] s t)
    (hH : linearEnvelope a j*m ≤ H)
    (i : (schedule k j).Constituent width) (e : Expr ((schedule k j).Constituent width))
    (he : e∈terminalFamilies k j width s t i) : e.FixedLogBound H := by
  have hH0 : 0 ≤ H := (mul_nonneg (linearEnvelope_pos ha j).le (by linarith)).trans hH
  have hone : 1 ≤ Real.exp H := Real.one_le_exp_iff.mpr hH0
  exact obstructionExpressions_fixedBound k j (ranges a m j) hone
    (fun path z hz=>(actual_frequency_abs_le_exp ha hm j path z hz).trans
      (Real.exp_le_exp.mpr hH)) [] false s _ t (sampledExpressions_fixedBound k j width hone) ht e
      (actualFamilies_obstructions _ _ _ _ _ _ _ false i e he)

theorem terminalFamilies_divisorsBelow (k j : ℕ) (width : Role→ℕ) (p : ℕ)
    (S : List Bool→Finset ℤ) (hS : ∀path s,s∈S path→|s| < (p:ℤ))
    (s : ℤ) (t : HistoryReconstruction.Tree j) (ht : RangeSupported S j [] s t)
    (i : (schedule k j).Constituent width) (e : Expr ((schedule k j).Constituent width))
    (he : e∈terminalFamilies k j width s t i) : e.DivisorsBelow p := by
  apply obstructionExpressions_divisorsBelow k j S p hS [] false s
    (sampledExpressions k j width) t ?_ ht e
    (actualFamilies_obstructions _ _ _ _ _ _ _ false i e he)
  intro u
  exact finiteProductExpression_divisorsBelow p _ (fun _=>trivial)

theorem eventually_terminalFamilies_syntax (k : ℕ) :
    ∀ᶠL : ℝ in atTop,∀(d : Decomposition) (E : Finset ℕ) (δ α β ρ γ c₀ c BD : ℝ),
      ∀(s : SelectedWordSource d E δ L k α β ρ γ c₀) (w : FixedConfigurationWitness s c BD)
      (j : ℕ) (r : ℤ) (t : HistoryReconstruction.Tree j) i e,
      e∈terminalFamilies k j (sourceWidth w.configuration (wordSize k L)) r t i →
      e.syntaxSize ≤ 6*obstructionSizeFactor k j*(wordSize k L+1) := by
  filter_upwards [eventually_terminal_sourceWidth_le k] with L hL
  intro d E δ α β ρ γ c₀ c BD s w j r t i e he
  have hh := terminalFamilies_syntax k j _ _ (hL d E δ α β ρ γ c₀ c BD s w) r t i e he
  exact hh.trans (by nlinarith)

theorem eventually_terminalFamilies_fixedLog (k : ℕ) (β BD : ℝ)
    (hβ : -1 < β) (hBD : 0 ≤ BD) :
    ∀ᶠL : ℝ in atTop,∀(d : Decomposition) (E : Finset ℕ) (δ α ρ γ c₀ c : ℝ),
      ∀(s : SelectedWordSource d E δ L k α β ρ γ c₀) (w : FixedConfigurationWitness s c BD)
      (h : SourceHistory (k:=k) (L:=L) (BD:=BD) k) i e,
      e∈terminalFamilies k k (sourceWidth w.configuration (wordSize k L)) h.val.1 h.val.2 i →
      e.FixedLogBound (Real.exp ((β+1)*L)) := by
  let a := BD+20*Real.log (depthScale k)
  have ha : 0 ≤ a := add_nonneg hBD (mul_nonneg (by norm_num)
    (Real.log_nonneg (one_le_depthScale k)))
  filter_upwards [eventually_historyPolynomialCost_le (linearEnvelope a k) (depthScale k) 1
    (depthScale_pos k).le (show 0 < β+1 by linarith) (by norm_num : (0:ℝ) < 1),
    (wordSize_tendsto k).eventually_ge_atTop 1] with L henv hm
  intro d E δ α ρ γ c₀ c s w h i e he
  apply terminalFamilies_fixedLog ha hm k k _ h.val.1 h.val.2 h.property ?_ i e he
  have hh : linearEnvelope a k*(1+(wordSize k L:ℝ)) ≤ Real.exp ((β+1)*L) := by
    simpa only [historyPolynomialCost,pow_one,one_mul,wordSize] using henv
  nlinarith [linearEnvelope_pos ha k]

end Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval

end

end OAI
