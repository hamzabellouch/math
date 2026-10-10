import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalMaskedNorm

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds HigherBiasSourceWord
open DiagonalEstimate ParityActions Filter
attribute [local instance] Classical.propDecidable

theorem eventually_sourceTerminalMaskedFactors_norms (k : ℕ) (BD c α : ℝ)
    (hBD : 0≤BD) (hα : 0<α) :
    ∀ᶠ ℓ : ℝ in atTop, ∀(d : Decomposition)(E : Finset ℕ)(δ β ρ γ c₀ : ℝ),
      (∀q∈E,α*ℓ≤Real.log (Real.log q) ∧ Real.log (Real.log q)≤β*ℓ) →
      ∀(s : SelectedWordSource d E δ ℓ k α β ρ γ c₀)(w : FixedConfigurationWitness s c BD),
      ∀n,n+1≤k → ∀(σ τ : Reassignments k n (wordSize k ℓ))
        (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) (n+1)),h.val.1=h'.val.1 →
      ∀(masks : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→ℕ→ℂ),
        (∀i q,‖masks i q‖≤1) →
      ∀p : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q,
        (productPrior (sourceTerminalCoordinatePrior w n)).mass p≠0 →
      ∀L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)),
        (∀q∈sourceScheduledShells w (n+1) L,
          ‖sourceTerminalMaskedLongFactor w n σ τ masks p L S h.val.1 h.val.2 h'.val.2 q.val‖≤1) ∧
        (∀q∈sourceScheduledShells w (n+1) S,
          ‖sourceTerminalMaskedShortFactor w n σ τ masks p L S h.val.1 h.val.2 h'.val.2 q.val‖≤1) := by
  filter_upwards [actualFrequencyCutoff_eventually k hBD hα] with ℓ hfreq
  intro d E δ β ρ γ c₀ hband s w n hn σ τ h h' hroot masks hm p hmass L S
  apply sourceTerminalMaskedFactors_norms_of_mass w n σ τ masks hm h h' hroot
    (hfreq.1 (n+1) hn) _ p hmass L S
  intro i q hq
  exact hfreq.2 q.val (fixedConfiguration_scheduled_log_bounds w hband (n+1) i q hq).1

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
