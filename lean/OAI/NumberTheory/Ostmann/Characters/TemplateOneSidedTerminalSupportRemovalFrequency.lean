import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedTerminalIntegerPrior
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedTerminalSupportRemovalBudget

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval
open Template SymbolicHistory TemplateOneSidedBudget TemplateOneSidedSupportTelescoping
open HigherBiasSource HigherBiasSource.SourceTemplate DiagonalEstimate InitialCharacterScale
open HistoryFrequencyLabels HistoryFrequencyBudget Filter
attribute [local instance] Classical.propDecidable

theorem eventually_terminalFamilies_divisorsBelow (k : ℕ) {BD α : ℝ}
    (hBD : 0 ≤ BD) (hα : 0 < α) :
    ∀ᶠL : ℝ in atTop,∀(d : Decomposition)(E : Finset ℕ)(δ β ρ γ c₀ c : ℝ),
    (∀p∈E,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
    ∀(s : SelectedWordSource d E δ L k α β ρ γ c₀)(w : FixedConfigurationWitness s c BD)
      (n : ℕ),n+1 ≤ k → ∀(h : SourceHistory (k:=k) (L:=L) (BD:=BD) (n+1)) i e,
      e∈terminalFamilies k (n+1) (sourceWidth w.configuration (wordSize k L)) h.val.1 h.val.2 i →
      ∀u a,a∈terminalSourceIntegerSupport w n u → e.DivisorsBelow a.toNat := by
  filter_upwards [actualFrequencyCutoff_eventually k hBD hα] with L hL
  intro d E δ β ρ γ c₀ c hband s w n hn h i e he u a ha
  rw [terminalSourceIntegerSupport_eq_nat_image] at ha
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
  have hp0 : (0:ℝ) < p := by exact_mod_cast (terminalSourceNaturalSupport_prime w n u hp).pos
  have hb := (terminalSourceIntegerSupport_bounds w n hband u
    (by rw [terminalSourceIntegerSupport_eq_nat_image]; exact Finset.mem_image.mpr ⟨p,hp,rfl⟩)).1
  have hlog : Real.exp (α*L) ≤ Real.log p := by
    have hh := Real.log_le_log (Real.exp_pos (Real.exp (α*L))) (by simpa only [Int.cast_natCast] using hb)
    simpa only [Real.log_exp] using hh
  have hcut := hL.2 p hlog
  apply terminalFamilies_divisorsBelow k (n+1) _ p
    (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) (n+1)) ?_
    h.val.1 h.val.2 h.property i e he
  intro path f hf
  have hh := ((hL.1 (n+1) hn path f hf).2).trans_lt hcut
  have hh' : (f.natAbs:ℤ) < (p:ℤ) := by exact_mod_cast hh
  simpa only [Int.natCast_natAbs] using hh'

end Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval

end

end OAI
