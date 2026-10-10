import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateFrequencyScales
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateNormInputs
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinSourceNorm
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSourceScalesShells

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds HigherBiasSourceWord
open DiagonalEstimate
attribute [local instance] Classical.propDecidable
section
variable {d : Decomposition} {E : Finset ℕ} {δ ℓ α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ ℓ k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ)

theorem sourceSurvivorShells_subset (i) : sourceSurvivorShells w j i⊆s.locations.primes := by
  cases i with
  | inl i => exact fixedConfiguration_scheduled_shell_subset w j _
  | inr i => exact fixedConfiguration_scheduled_shell_subset w j _

theorem sourceSurvivorPrior_mem_of_mass_ne_zero
    (p : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (hp : (sourceSurvivorPrior w j).mass p≠0) (i) : p i∈sourceSurvivorShells w j i := by
  rw [sourceSurvivorPrior_eq_product] at hp
  exact primeProductPrior_mem_of_mass_ne_zero (sourceSurvivorShells w j)
    (sourceSurvivorShells_pos w j) p hp i

theorem sourceSurvivorShells_family_order (i) (q : PrimeUpTo s.locations.Q)
    (hq : q∈sourceSurvivorShells w j i) : 2<orderOf (familyCharacter s.family q.val) := by
  simpa only [familyCharacter,q.property,dite_true] using
    s.family.higher_order q (sourceSurvivorShells_subset w j i hq)

end
end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
