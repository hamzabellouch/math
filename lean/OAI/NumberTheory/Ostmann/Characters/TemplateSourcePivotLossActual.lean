import OAI.NumberTheory.Ostmann.Characters.SourceTemplateShells
import OAI.NumberTheory.Ostmann.Characters.TemplateSourceIteration
import OAI.NumberTheory.Ostmann.Characters.TemplateSourcePivotLossBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template InitialCharacterScale DiagonalEstimate
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}

theorem sourcePivotNormalization_cell_mass (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j<k)
    (a : Fin (sourceWidth w.configuration (wordSize k L)
      ((schedule k j).role (pivotSlot k j hj).val))) :
    c/Real.exp (β*L) ≤ primeShellMass
      (scheduledPrimeShells k (sourceWidth w.configuration (wordSize k L))
        (sourceScheduledShells w 0) j ⟨(pivotSlot k j hj).val,a⟩) := by
  obtain ⟨n,hn⟩ := w.nonempty
  have hc : ∀i,c/Real.exp (β*L) ≤
      primeShellMass (configurationCells s.locations.primes w.configuration i) := by
    intro i
    exact (w.good n hn i).2.2.1
  change c/Real.exp (β*L) ≤ primeShellMass
    (scheduledPrimeShells k (sourceWidth w.configuration (wordSize k L))
      (configurationPrimeShells w.configuration (wordSize k L)
        (s.locations.base 0) (s.locations.base 2) s.locations.primes) j
      ⟨(pivotSlot k j hj).val,a⟩)
  apply scheduledPrimeShells_nonword_mass _ _ _ _ _ _ _ hc
  rw [(pivotSlot k j hj).property.2]
  exact Role.noConfusion

theorem sourcePivotNormalization_count (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j<k) :
    (sourceWidth w.configuration (wordSize k L)
      ((schedule k j).role (pivotSlot k j hj).val) : ℝ) ≤ sourcePivotCountBound k := by
  have hw : sourceWidth w.configuration (wordSize k L)
      ((schedule k j).role (pivotSlot k j hj).val) =
      (w.configuration.2 (Fin.castSucc ⟨j,hj⟩)).length := by
    rw [(pivotSlot k j hj).property.2]
    exact sourceWidth_pivot w.configuration (wordSize k L) ⟨j,hj⟩
  rw [hw]
  exact w.geometry.length_upper _

theorem sourcePivotNormalization_le_loss (w : FixedConfigurationWitness s c BD)
    (hc : 0<c) (hL : 0≤L) (hLc : -Real.log c≤L) (j : ℕ) (hj : j<k) :
    sourcePivotNormalization w j hj ≤ Real.exp (sourcePivotLoss β k L j) := by
  unfold sourcePivotNormalization scheduledPivotFactor
  apply pivot_factor_le_sourcePivotLoss _ β L c k j hc hL hLc
  · exact sourcePivotNormalization_cell_mass w j hj
  · exact sourcePivotNormalization_count w j hj

end
end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
