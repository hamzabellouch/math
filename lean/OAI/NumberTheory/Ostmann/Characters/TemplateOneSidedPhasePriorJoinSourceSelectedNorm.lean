import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinSourceSelectedNormBasic

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
    (j : ℕ) (hj : j<k)

theorem sourceSelectedFactors_norms_of_mass {V : ℕ}
    (σ ρ : Equiv.Perm (ActualCopied w.configuration (wordSize k ℓ) j))
    (masks : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k ℓ))→ℕ→ℂ)
    (hmasks : ∀i q,‖masks i q‖≤1)
    (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) j) (hroot : h.val.1=h'.val.1)
    (hrange : ∀path f,
      f∈ranges (BD+20*Real.log (depthScale k)) (wordSize k ℓ:ℝ) j path→f≠0 ∧ f.natAbs≤V)
    (hV : ∀i q,q∈sourceSurvivorShells w j i→V<q.val)
    (p : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (hmass : (sourceSurvivorPrior w j).mass p≠0)
    (L S : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k ℓ))) (hLS : L≠S)
    (P : ℕ+) :
    (∀q∈sourceSurvivorShells w j L,
      ‖sourceLongFactor w.configuration (wordSize k ℓ) j hj σ ρ (familyCharacter s.family)
        (sourceScheduledUnits w j) masks p L S P h.val.1 h.val.2 h'.val.2 q.val‖≤1) ∧
    (∀q∈sourceSurvivorShells w j S,
      ‖sourceShortFactor w.configuration (wordSize k ℓ) j hj σ ρ (familyCharacter s.family)
        (sourceScheduledUnits w j) masks p L S P h.val.1 h.val.2 h'.val.2 q.val‖≤1) := by
  apply sourceFactors_norms_on_sources w.configuration (wordSize k ℓ) j hj σ ρ
    (familyCharacter s.family) (sourceScheduledUnits w j)
    (fixedConfiguration_scheduled_unit_norm w j) masks hmasks p L S hLS
    (sourceSurvivorShells w j L) (sourceSurvivorShells w j S)
    (sourceSurvivorShells_pos w j L) (sourceSurvivorShells_pos w j S) _ _ _
    _ hrange h h' hroot P
  · intro i _
    have hp := sourceSurvivorPrior_mem_of_mass_ne_zero w j p hmass i
    exact ⟨sourceSurvivorShells_family_order w j i (p i) hp,hV i (p i) hp⟩
  · intro q hq
    exact ⟨sourceSurvivorShells_family_order w j L q hq,hV L q hq⟩
  · intro q hq
    exact ⟨sourceSurvivorShells_family_order w j S q hq,hV S q hq⟩

theorem sourceSelected_exposedCharacter_ne_one
    (S : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k ℓ)))
    (q : PrimeUpTo s.locations.Q) (hq : q∈sourceSurvivorShells w j S) (positive : Bool) :
    exposedCharacter
      (sourceSliceCharacters w.configuration (wordSize k ℓ) j hj s.locations.Q
        (familyCharacter s.family) S q.val) positive≠1 :=
  sourceSlice_exposedCharacter_ne_one w.configuration (wordSize k ℓ) j hj
    (familyCharacter s.family) S q (sourceSurvivorShells_family_order w j S q hq) positive

end
end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
