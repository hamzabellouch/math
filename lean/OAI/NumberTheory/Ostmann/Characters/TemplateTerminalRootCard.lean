import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyBudgetAbsorption
import OAI.NumberTheory.Ostmann.Characters.TemplateTerminalFrequency

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
open Filter HistoryFrequencyBudget TemplateNormAsymptotic

theorem terminalRoot_card (a m : ℝ) (j : ℕ) :
    Fintype.card ↥(ranges a m j [])=2*bound a m j := by
  change Fintype.card {s : ℤ // s∈signedRange (bound a m j)}=2*bound a m j
  rw [Fintype.card_coe,signedRange_card]

theorem terminalRoot_card_le (a m : ℝ) (j : ℕ) :
    (Fintype.card ↥(ranges a m j []) : ℝ) ≤ 2*Real.exp (exponent a m j) := by
  rw [terminalRoot_card,Nat.cast_mul,Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_left (bound_le_exp a m j) (by norm_num)

theorem terminalRoot_card_eventually (j : ℕ) {z a δ : ℝ} (hz : 0<z) (hδ : 0<δ) :
    ∀ᶠ L : ℝ in atTop,
      (Fintype.card ↥(ranges a (⌊z*L⌋₊ : ℝ) j []) : ℝ) ≤
        2*Real.exp (((2:ℝ)^j*a+δ)*(⌊z*L⌋₊ : ℝ)) := by
  have hs := (word_tendsto hz).eventually (eventually_const_sqrt_le (2*(4:ℝ)^j) 0 δ hδ)
  filter_upwards [hs] with L hL
  apply (terminalRoot_card_le a (⌊z*L⌋₊ : ℝ) j).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  unfold exponent
  nlinarith

end Ostmann.Characters.Template

end

end OAI
