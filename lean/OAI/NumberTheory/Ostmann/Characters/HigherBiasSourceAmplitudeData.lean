import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceBounds
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceConfigurationCost
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceConfigurationRolesCells
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceFixedConfigurationDefs
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceHalfProduct

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Construction Preliminaries HigherBiasSourceWord HigherBiasSourceRoleBounds InitialCharacterScale
open scoped BigOperators

structure FixedConfigurationWitness {d : Decomposition} {E : Finset ℕ} {δ L : ℝ}
    {k : ℕ} {α β ρ γ c₀ : ℝ} (s : SelectedWordSource d E δ L k α β ρ γ c₀)
    (c BD : ℝ) where
  configuration : SourceConfiguration k
  endpoints : Finset ℤ
  subset : endpoints ⊆ s.endpoints
  geometry : ConfigurationGeometry s c BD configuration
  good : ∀ n∈endpoints,ConfigurationGoodAt s c configuration n
  population : Real.exp (-selectionCost β (δ/2)*(wordSize k L:ℝ)-
    configurationLossCoefficient β*maxCells 4 k*L) ≤ (endpoints.card:ℝ)/Real.sqrt s.locations.X

namespace FixedConfigurationWitness
variable {d : Decomposition} {E : Finset ℕ} {δ L : ℝ} {k : ℕ} {α β ρ γ c₀ c BD : ℝ}
variable {s : SelectedWordSource d E δ L k α β ρ γ c₀}

theorem nonempty (w : FixedConfigurationWitness s c BD) : w.endpoints.Nonempty := by
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  have hh := w.population
  rw [he,Finset.card_empty,Nat.cast_zero,zero_div] at hh
  exact (not_le_of_gt (Real.exp_pos _)) hh

def cells (w : FixedConfigurationWitness s c BD) :
    Fin (configCellCount w.configuration)→Finset (PrimeUpTo s.locations.Q) :=
  configurationCells s.locations.primes w.configuration

theorem cells_pos (w : FixedConfigurationWitness s c BD) : ∀ i,0 < primeShellMass (w.cells i) := by
  obtain ⟨n,hn⟩ := w.nonempty
  intro i
  obtain ⟨hp,_⟩ := (w.good n hn i).2.2.2
  exact hp

def roles (w : FixedConfigurationWitness s c BD) :
    Fin ((wordSize k L+1)+configCellCount w.configuration)→Finset (PrimeUpTo s.locations.Q) :=
  halfRoleShells (s.locations.base 0) (s.locations.base 2) (wordSize k L) w.cells

theorem roles_pos (w : FixedConfigurationWitness s c BD) : ∀ i,0 < primeShellMass (w.roles i) :=
  halfRole_mass_pos _ _ _ _ s.bulk_pos s.top_pos w.cells_pos

theorem roles_subset (w : FixedConfigurationWitness s c BD) : ∀ i,w.roles i⊆s.locations.primes := by
  apply sourceHalf_subsets
  · exact boundedInterval_subset _ _ _
  · exact boundedInterval_subset _ _ _
  · intro i
    exact Finset.filter_subset _ _

def amplitude (w : FixedConfigurationWitness s c BD) : ℂ :=
  initialCharacterAmplitude (characterDoubleShell w.roles)
    (characterDoubleShell_positive w.roles w.roles_pos)
    (characterDoubleChar (fun _=>familyCharacter s.family))
    (characterDoubleCenter (fun _=>familyCenter s.family))
    (characterDoublePhase (fun _=>familyPhase s.family))
    (characterDoubleMask (sourceHalfMask s.J)) s.locations.X

theorem endpoint_mean (w : FixedConfigurationWitness s c BD) (hδ : 0 ≤ δ) :
    ∀ n∈w.endpoints,Real.exp (-selectionCost β (δ/2)*(wordSize k L:ℝ))*(δ/4)^configCellCount w.configuration ≤
      ‖initialCharacterMean w.roles w.roles_pos (fun _=>familyCharacter s.family)
        (fun _=>familyCenter s.family) (fun _=>familyPhase s.family) (sourceHalfMask s.J) n‖ := by
  intro n hn
  apply sourceHalfMean_lower s.family _ _ _ s.bulk_pos s.top_pos w.cells_pos s.J n
    (Real.exp_pos _).le (by positivity) (s.word_mean n (w.subset hn))
  intro i
  obtain ⟨hp,hm⟩ := (w.good n hn i).2.2.2
  exact hm

end FixedConfigurationWitness
end Ostmann.Characters.HigherBiasSource

end

end OAI
