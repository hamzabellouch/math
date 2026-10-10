import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceAmplitudeData
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceFixedConfigurationIdentity
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateLeafMask

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template InitialCharacterScale HigherBiasSourceRoleBounds
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem fixedConfiguration_product_window {d : Decomposition} {E : Finset ℕ}
    {δ L : ℝ} {k : ℕ} {α β ρ γ c₀ c BD : ℝ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD) (hX : 0 < (s.locations.X:ℝ))
    (q : Fin (sourceHalfSize w.configuration (wordSize k L)+
      sourceHalfSize w.configuration (wordSize k L)) → PrimeUpTo s.locations.Q)
    (hq : ∀ i,q i∈characterDoubleShell w.roles i)
    (hmask : characterDoubleMask (sourceHalfMask s.J) q ≠ 0) :
    (s.locations.X:ℝ)*Real.exp (initialGap BD k L-configurationProductWidth k c) ≤
      (characterTupleProduct q:ℝ) ∧
    (characterTupleProduct q:ℝ) ≤
      (s.locations.X:ℝ)*Real.exp (initialGap BD k L+configurationProductWidth k c) := by
  apply source_doubled_product_window (s.locations.base 0) (s.locations.base 2)
    s.locations.primes w.configuration w.roles_pos s.J
    (configurationTarget (Real.log s.locations.X) s.J (gapSchedule BD k L) w.configuration)
    hX w.geometry.target_error ?_ ?_ q hq hmask
  · simpa only [gapSchedule_zero] using configuration_targets_total_identity
      (Real.log s.locations.X) s.J (gapSchedule BD k L) w.configuration
  · intro j
    simpa only [show 2*((1/10000:ℝ)*k)=2*(k:ℝ)/10000 by ring] using w.geometry.length_upper j

theorem fixedConfiguration_X_pos {d : Decomposition} {E : Finset ℕ}
    {δ L : ℝ} {k : ℕ} {α β ρ γ c₀ c BD : ℝ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD) : 0 < (s.locations.X:ℝ) := by
  by_contra hn
  have hz : (s.locations.X:ℝ) = 0 := le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg _)
  have hh := w.population
  rw [hz,Real.sqrt_zero,div_zero] at hh
  exact (not_le_of_gt (Real.exp_pos _)) hh

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
