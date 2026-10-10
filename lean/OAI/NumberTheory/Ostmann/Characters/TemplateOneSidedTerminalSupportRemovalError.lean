import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedTerminalSupportRemovalEstimate
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedTerminalSupportRemovalLiteral

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval
open Template Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale HistoryFrequencyLabels HistoryFrequencyBudget DiagonalEstimate ParityActions Filter
attribute [local instance] Classical.propDecidable

theorem eventually_terminal_mean_sub_core_le (n : ℕ)
    {α β ρ γ c₀ c BD : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hc₀ : 0 < c₀) (hc : 0 < c) (hBD : 0 ≤ BD) :
    ∀ᶠL : ℝ in atTop,
    ∀(d : Decomposition)(E : Finset ℕ)(δ : ℝ),(∀p∈E,p.Prime) →
      (∀p∈E,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      ∀s : SelectedWordSource d E δ L (n+1) α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
      ∀(B V : (l:ℕ)→State (n+1) (l+1)→ℤ)
        (σ τ : Reassignments (n+1) n (wordSize (n+1) L))
        (h h' : SourceHistory (k:=n+1) (L:=L) (BD:=BD) (n+1)),h.val.1=h'.val.1 →
      ‖SourceTemplate.sourceHistoryPairMean w B V n σ τ h h'-terminalCoreMean w n B V σ τ h h'‖ ≤
        Real.exp (-(1/8:ℝ)*Real.exp (α*L)) := by
  obtain ⟨K,hK,hbound⟩ := exists_eventually_terminal_support_removal n hα hαβ hρ hγ hc₀ hc hBD
  filter_upwards [hbound,eventually_historyPolynomialCost_le K 1 2 (by norm_num) hα
    (by norm_num : (0:ℝ) < 1/8),eventually_ge_atTop (0:ℝ)] with L hL hsmall hL0
  intro d E δ hE hband s w B V σ τ h h' hroot
  rw [terminal_sourceHistoryPairMean_eq_start w n B V (le_refl _) σ τ h h' hroot]
  apply (hL d E δ hE hband s w B V σ τ h h' hroot).trans
  apply Real.exp_le_exp.mpr
  have hfloor : L ≤ 1+(⌊L⌋₊:ℝ) := by
    have hh := Nat.lt_floor_add_one L
    linarith
  have hcost : K*L^2 ≤ historyPolynomialCost K 1 2 L := by
    simp only [historyPolynomialCost,one_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hfloor 2) hK.le
  linarith

end Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval

end

end OAI
