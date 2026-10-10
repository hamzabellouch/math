import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateIntegerPriorSource
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinEdge
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSourceScalesBands

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSourceScales
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate Template
open DiagonalEstimate HigherBiasSourceWord Template.OneSidedPhase InitialCharacterScale
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD)

theorem sourceSurvivorCoordinatePrior_eq (j : ℕ) (i : SurvivingPrimeIndex k j
    (sourceWidth w.configuration (wordSize k L))) :
    sourceSurvivorCoordinatePrior w j i =
      primeShellPrior (sourceSurvivorShells w j i) (sourceSurvivorShells_pos w j i) := by
  cases i <;> rfl

theorem sourceSurvivorShells_log_bounds
    (hband : ∀p∈E,α*L≤Real.log (Real.log p) ∧ Real.log (Real.log p)≤β*L)
    (j : ℕ) (i : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)))
    (p : PrimeUpTo s.locations.Q) (hp : p∈sourceSurvivorShells w j i) :
    Real.exp (α*L)≤Real.log p.val ∧ Real.log p.val≤Real.exp (β*L) := by
  cases i <;> exact fixedConfiguration_scheduled_log_bounds w hband j _ p hp

theorem sourceSurvivorShells_bulk (j : ℕ) (z : Word k j × Fin (wordSize k L)) :
    sourceSurvivorShells w j (.inl (copiedBulk w.configuration (wordSize k L) j z)) =
      s.locations.base 0 := by
  exact actualCopiedShells_bulk w.configuration (wordSize k L) j
    (s.locations.base 0) (s.locations.base 2) s.locations.primes _
    (copiedBulk_isBulk w.configuration (wordSize k L) j z)

theorem sourceSurvivorShells_retired (j : ℕ) (hj : j≤k) (big : Bool) (a : Fin j) (b : Bool) :
    sourceSurvivorShells w j (.inr (copiedRetiredOutside w.configuration (wordSize k L) j hj big a b)) =
      boundedRawLogCell s.locations.primes
        (w.configuration.1 (anchorCoordinate ⟨a.val,a.isLt.trans_le hj⟩ big)) := by
  change sourceScheduledShells w j (copiedRetiredAnchor w.configuration (wordSize k L) j hj big a b) = _
  exact scheduledPrimeShells_anchor w.configuration (wordSize k L) j
    (s.locations.base 0) (s.locations.base 2) s.locations.primes
    (retiredAnchors k j hj big a b).val ⟨a.val,a.isLt.trans_le hj⟩ big
    (retiredAnchors k j hj big a b).property.2 _

theorem sourceSurvivorShells_retired_log_bounds (j : ℕ) (hj : j≤k)
    (big : Bool) (a : Fin j) (b : Bool) (p : PrimeUpTo s.locations.Q)
    (hp : p∈sourceSurvivorShells w j
      (.inr (copiedRetiredOutside w.configuration (wordSize k L) j hj big a b))) :
    Real.exp (if big then s.locations.u else s.locations.s)≤Real.log p.val ∧
      Real.log p.val≤Real.exp ((if big then s.locations.u else s.locations.s)+1) := by
  rw [sourceSurvivorShells_retired] at hp
  exact fixedConfiguration_anchor_log_bounds w _ big p hp

end
end Ostmann.Characters.TemplateOneSidedSourceScales

end

end OAI
