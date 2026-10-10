import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceAmplitudeData
import OAI.NumberTheory.Ostmann.Characters.SourceTemplatePhaseDefs
import OAI.NumberTheory.Ostmann.Characters.SourceTemplatePriors

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template HigherBiasSourceWord InitialCharacterScale
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

theorem sourceCharacterData_nonprincipal {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (E : Fin (sourceHalfSize cfg m) → Finset (PrimeUpTo Q))
    (χ : Fin (sourceHalfSize cfg m) → (q:ℕ) → MulChar (ZMod q) ℂ)
    (hχ : ∀ i,∀ p∈E i,χ i p.val ≠ 1)
    (i : SourceConstituent cfg m) (p : PrimeUpTo Q) (hp : p∈sourcePrimeShells cfg m E i) :
    sourceCharacterData cfg m χ i p ≠ 1 := by
  unfold sourceCharacterData
  change p∈characterDoubleShell E (sourceIndexEquiv cfg m i) at hp
  generalize sourceIndexEquiv cfg m i = j at hp ⊢
  refine Fin.addCases (fun a => ?_) (fun a => ?_) j hp
  · intro h
    simpa only [characterDoubleChar,Fin.append_left] using
      hχ a p (by simpa only [characterDoubleShell,Fin.append_left] using h)
  · intro h
    have hc := hχ a p (by simpa only [characterDoubleShell,Fin.append_right] using h)
    simp only [characterDoubleChar,Fin.append_right]
    intro he
    apply hc
    have hh := congrArg star he
    simpa only [star_star,star_one] using hh

theorem fixedConfiguration_character_nonprincipal {d : Decomposition} {E : Finset ℕ}
    {δ L : ℝ} {k : ℕ} {α β ρ γ c₀ c BD : ℝ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD)
    (i : SourceConstituent w.configuration (wordSize k L)) (p : PrimeUpTo s.locations.Q)
    (hp : p∈sourcePrimeShells w.configuration (wordSize k L) w.roles i) :
    sourceCharacterData w.configuration (wordSize k L) (fun _=>familyCharacter s.family) i p ≠ 1 := by
  apply sourceCharacterData_nonprincipal w.configuration (wordSize k L) w.roles
    (fun _=>familyCharacter s.family) _ i p hp
  intro j q hq
  exact s.family.characterNat_nonprincipal (w.roles_subset j hq)

theorem fixedConfiguration_unit_norm {d : Decomposition} {E : Finset ℕ}
    {δ L : ℝ} {k : ℕ} {α β ρ γ c₀ c BD : ℝ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD)
    (i : SourceConstituent w.configuration (wordSize k L)) (p : PrimeUpTo s.locations.Q) :
    ‖sourceUnitData w.configuration (wordSize k L) (fun _=>familyPhase s.family) i p‖ = 1 :=
  norm_sourceUnitData w.configuration (wordSize k L) (fun _=>familyPhase s.family)
    (fun _ q=>familyPhase_norm s.family q.val) i p

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
