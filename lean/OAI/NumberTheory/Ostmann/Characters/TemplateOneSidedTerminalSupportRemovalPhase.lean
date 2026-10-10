import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalPhaseNorm
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedTerminalIntegerPriorProperties
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedTerminalSupportRemovalDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval
open Construction Preliminaries Template Template.OneSidedPhase TemplateSupportRemoval
open HigherBiasSource HigherBiasSource.SourceTemplate InitialCharacterScale DiagonalEstimate
open HistoryFrequencyLabels HistoryFrequencyBudget ParityActions Filter
attribute [local instance] Classical.propDecidable

theorem terminalSource_mass_ne_zero {d : Decomposition} {E : Finset ℕ}
    {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (n : ℕ) (p : terminalSourceIndex w n→PrimeUpTo s.locations.Q)
    (hp : ∀i,p i∈sourceScheduledShells w (n+1) i) :
    (productPrior (sourceTerminalCoordinatePrior w n)).mass p≠0 := by
  change (∏i,(sourceTerminalCoordinatePrior w n i).mass (p i))≠0
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  rw [←terminalSourceIntegerWeight_cast w n i]
  exact ne_of_gt ((terminalSourceIntegerWeight_pos_iff w n i _).mpr
    (Finset.mem_image.mpr ⟨p i,hp i,rfl⟩))

theorem eventually_terminalIntegerPhase_norm (k : ℕ) (BD c α : ℝ)
    (hBD : 0 ≤ BD) (hα : 0 < α) :
    ∀ᶠL : ℝ in atTop,∀(d : Decomposition)(E : Finset ℕ)(δ β ρ γ c₀ : ℝ),
      (∀q∈E,α*L ≤ Real.log (Real.log q) ∧ Real.log (Real.log q) ≤ β*L) →
      ∀(s : SelectedWordSource d E δ L k α β ρ γ c₀)(w : FixedConfigurationWitness s c BD),
      ∀n,n+1 ≤ k → ∀(σ τ : Reassignments k n (wordSize k L))
        (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) (n+1)),h.val.1=h'.val.1 →
      ∀x : terminalSourceIndex w n→ℤ,(∀i,x i∈terminalSourceIntegerSupport w n i) →
        ‖terminalIntegerPhase w n σ τ h h' x‖ ≤ 1 := by
  filter_upwards [eventually_sourceTerminal_guardedPhase_norm k BD c α hBD hα] with L hL
  intro d E δ β ρ γ c₀ hband s w n hn σ τ h h' hroot x hx
  obtain ⟨p,hp,rfl⟩ := terminalSource_support_exists_prime w n x hx
  rw [terminalIntegerPhase,integerPrimeTest_at_prime]
  exact hL d E δ β ρ γ c₀ hband s w n hn σ τ h h' hroot p
    (terminalSource_mass_ne_zero w n p hp)

end Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval

end

end OAI
