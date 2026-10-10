import OAI.NumberTheory.Ostmann.Characters.TemplateTerminalGramAbsorption

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Filter HistoryFrequencyLabels HistoryFrequencyBudget

theorem terminalHistoryPair_card_eventually (j : ℕ) {z a α δ : ℝ}
    (hz : 0<z) (ha : 0≤a) (hα : 0<α) (hδ : 0<δ) :
    ∀ᶠ L : ℝ in atTop,
      (Fintype.card (SupportedHistory (ranges a (⌊z*L⌋₊ : ℝ) j) j []) : ℝ)^2*
        Real.exp (-δ*Real.exp (α*L)) ≤ Real.exp (-(δ/2)*Real.exp (α*L)) := by
  filter_upwards [terminalHistoryPair_sum_eventually j hz ha hα hδ] with L hL
  have hh := hL (fun _ _ => (Real.exp (-δ*Real.exp (α*L)):ℂ)) (by
    intro h h'
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact le_rfl)
  have he : ‖∑_h : SupportedHistory (ranges a (⌊z*L⌋₊ : ℝ) j) j [],
      ∑_h' : SupportedHistory (ranges a (⌊z*L⌋₊ : ℝ) j) j [],
      (Real.exp (-δ*Real.exp (α*L)):ℂ)‖ =
      (Fintype.card (SupportedHistory (ranges a (⌊z*L⌋₊ : ℝ) j) j []) : ℝ)^2*
        Real.exp (-δ*Real.exp (α*L)) := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,norm_mul,
      Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    ring
  rwa [he] at hh

end Ostmann.Characters.Template

end

end OAI
