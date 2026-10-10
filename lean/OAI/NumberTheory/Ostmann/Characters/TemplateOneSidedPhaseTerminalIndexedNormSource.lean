import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalIndexedNorm

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds HigherBiasSourceWord
open DiagonalEstimate ParityActions
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ ℓ α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ ℓ k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (n : ℕ)

theorem sourceTerminalFactors_norms_of_mass {V : ℕ}
    (σ τ : Reassignments k n (wordSize k ℓ))
    (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) (n+1))
    (hroot : h.val.1=h'.val.1)
    (hrange : ∀path f,
      f∈ranges (BD+20*Real.log (depthScale k)) (wordSize k ℓ:ℝ) (n+1) path →
        f≠0 ∧ f.natAbs≤V)
    (hV : ∀i q,q∈sourceScheduledShells w (n+1) i→V<q.val)
    (p : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (hmass : (productPrior (sourceTerminalCoordinatePrior w n)).mass p≠0)
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))) :
    (∀q∈sourceScheduledShells w (n+1) L,
      ‖sourceTerminalLongFactor w n σ τ p L S h.val.1 h.val.2 h'.val.2 q.val‖≤1) ∧
    (∀q∈sourceScheduledShells w (n+1) S,
      ‖sourceTerminalShortFactor w n σ τ p L S h.val.1 h.val.2 h'.val.2 q.val‖≤1) := by
  have hp (i) : p i∈sourceScheduledShells w (n+1) i :=
    primeProductPrior_mem_of_mass_ne_zero (sourceScheduledShells w (n+1))
      (sourceScheduledShells_pos w (n+1)) p hmass i
  apply sourceTerminalFactors_norms_on_sources w n σ τ h h' hroot hrange p L S
    (sourceScheduledShells w (n+1) L) (sourceScheduledShells w (n+1) S)
  · intro i _
    exact ⟨fixedConfiguration_scheduled_shell_subset w (n+1) i (hp i),hV i (p i) (hp i)⟩
  · intro q hq
    exact ⟨fixedConfiguration_scheduled_shell_subset w (n+1) L hq,hV L q hq⟩
  · intro q hq
    exact ⟨fixedConfiguration_scheduled_shell_subset w (n+1) S hq,hV S q hq⟩

theorem sourceTerminalFactors_norms_of_actual_cutoff
    (hBD : 0≤BD) (hm : 1≤wordSize k ℓ) (hn : n+1≤k)
    (σ τ : Reassignments k n (wordSize k ℓ))
    (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) (n+1))
    (hroot : h.val.1=h'.val.1)
    (hV : ∀i q,q∈sourceScheduledShells w (n+1) i→actualFrequencyCutoff k BD ℓ<q.val)
    (p : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (hmass : (productPrior (sourceTerminalCoordinatePrior w n)).mass p≠0)
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))) :
    (∀q∈sourceScheduledShells w (n+1) L,
      ‖sourceTerminalLongFactor w n σ τ p L S h.val.1 h.val.2 h'.val.2 q.val‖≤1) ∧
    (∀q∈sourceScheduledShells w (n+1) S,
      ‖sourceTerminalShortFactor w n σ τ p L S h.val.1 h.val.2 h'.val.2 q.val‖≤1) := by
  apply sourceTerminalFactors_norms_of_mass w n σ τ h h' hroot _ hV p hmass L S
  have ha : 0≤BD+20*Real.log (depthScale k) :=
    add_nonneg hBD (mul_nonneg (by norm_num) (Real.log_nonneg (one_le_depthScale k)))
  have hmR : (1:ℝ)≤wordSize k ℓ := by exact_mod_cast hm
  exact fun path f hf => ranges_le_uniform_terminalFrequencyCutoff ha hmR k (n+1) hn path f hf

theorem sourceTerminal_shell_exposedCharacter_ne_one
    (S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))
    (q : PrimeUpTo s.locations.Q) (hq : q∈sourceScheduledShells w (n+1) S) (positive : Bool) :
    exposedCharacter (sourceTerminalCharacters w n S q.val) positive≠1 :=
  sourceTerminal_exposedCharacter_ne_one w n S q
    (fixedConfiguration_scheduled_shell_subset w (n+1) S hq) positive

end
end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
