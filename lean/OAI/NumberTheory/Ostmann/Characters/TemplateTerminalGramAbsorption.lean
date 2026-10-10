import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGapSum
import OAI.NumberTheory.Ostmann.Characters.TemplateNormAsymptoticPrecision
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetHistoryCount
import OAI.NumberTheory.Ostmann.Characters.TemplateTerminalGramMean

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Filter HistoryFrequencyLabels HistoryFrequencyBudget TemplateOneSidedBudget TemplateNormAsymptotic

theorem terminalHistoryPair_sum_eventually (j : ℕ) {z a α δ : ℝ}
    (hz : 0<z) (ha : 0≤a) (hα : 0<α) (hδ : 0<δ) :
    ∀ᶠ L : ℝ in atTop,
      ∀F : SupportedHistory (ranges a (⌊z*L⌋₊ : ℝ) j) j [] →
        SupportedHistory (ranges a (⌊z*L⌋₊ : ℝ) j) j [] → ℂ,
      (∀h h',‖F h h'‖≤Real.exp (-δ*Real.exp (α*L))) →
      ‖∑h,∑h',F h h'‖≤Real.exp (-(δ/2)*Real.exp (α*L)) := by
  let C := 2*(fullNodeCount j:ℝ)*(Real.log 2+linearEnvelope a j)
  filter_upwards [eventually_scale_gap_finite_sum C z 1 hz.le hα hδ,
    (word_tendsto hz).eventually_ge_atTop 1] with L hL hm
  intro F hF
  have hh := hL (fun x : SupportedHistory (ranges a (⌊z*L⌋₊ : ℝ) j) j [] ×
      SupportedHistory (ranges a (⌊z*L⌋₊ : ℝ) j) j [] => F x.1 x.2) (by
    simpa only [historyPolynomialCost,pow_one,C] using supportedHistory_pair_card_le_exp ha hm j)
    (fun x => hF x.1 x.2)
  simpa only [Fintype.sum_prod_type] using hh

end Ostmann.Characters.Template

end

end OAI
