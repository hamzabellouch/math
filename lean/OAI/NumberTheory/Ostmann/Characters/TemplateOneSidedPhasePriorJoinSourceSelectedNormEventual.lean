import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinSourceSelectedNorm

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds HigherBiasSourceWord
open DiagonalEstimate Filter
attribute [local instance] Classical.propDecidable

theorem eventually_sourceSelectedFactors_norms (k : ℕ) (BD c α : ℝ)
    (hBD : 0≤BD) (hα : 0<α) :
    ∀ᶠ ℓ : ℝ in atTop, ∀(d : Decomposition)(E : Finset ℕ)(δ β ρ γ c₀ : ℝ),
      (∀q∈E,α*ℓ≤Real.log (Real.log q) ∧ Real.log (Real.log q)≤β*ℓ) →
      ∀(s : SelectedWordSource d E δ ℓ k α β ρ γ c₀)(w : FixedConfigurationWitness s c BD),
      ∀j (hj : j<k) (σ τ : Equiv.Perm (ActualCopied w.configuration (wordSize k ℓ) j)),
      ∀masks : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k ℓ))→ℕ→ℂ,
        (∀i q,‖masks i q‖≤1) →
      ∀(h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) j),h.val.1=h'.val.1 →
      ∀p : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q,
        (sourceSurvivorPrior w j).mass p≠0 →
      ∀L S : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k ℓ)),L≠S →
      ∀P : ℕ+,
        (∀q∈sourceSurvivorShells w j L,
          ‖sourceLongFactor w.configuration (wordSize k ℓ) j hj σ τ (familyCharacter s.family)
            (sourceScheduledUnits w j) masks p L S P h.val.1 h.val.2 h'.val.2 q.val‖≤1) ∧
        (∀q∈sourceSurvivorShells w j S,
          ‖sourceShortFactor w.configuration (wordSize k ℓ) j hj σ τ (familyCharacter s.family)
            (sourceScheduledUnits w j) masks p L S P h.val.1 h.val.2 h'.val.2 q.val‖≤1) := by
  filter_upwards [actualFrequencyCutoff_eventually k hBD hα] with ℓ hfreq
  intro d E δ β ρ γ c₀ hband s w j hj σ τ masks hmasks h h' hroot p hmass L S hLS P
  apply sourceSelectedFactors_norms_of_mass w j hj σ τ masks hmasks h h' hroot
    (hfreq.1 j hj.le) _ p hmass L S hLS P
  intro i q hq
  exact hfreq.2 q.val (TemplateOneSidedSourceScales.sourceSurvivorShells_log_bounds w hband j i q hq).1

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
