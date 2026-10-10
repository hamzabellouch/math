import OAI.NumberTheory.Ostmann.Characters.SourceTemplateCharacterLaw
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateShells
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceScheduledData
import OAI.NumberTheory.Ostmann.Characters.TemplateChosenPrime

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template HigherBiasSourceWord InitialCharacterScale
attribute [local instance] Classical.propDecidable

theorem sourcePrimeShells_subset {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (E : Fin (sourceHalfSize cfg m) → Finset (PrimeUpTo Q)) (G : Finset (PrimeUpTo Q))
    (hE : ∀ i,E i⊆G) (i : SourceConstituent cfg m) : sourcePrimeShells cfg m E i⊆G := by
  have hd : ∀ j,characterDoubleShell E j⊆G := by
    intro j
    refine Fin.addCases (fun a=>?_) (fun a=>?_) j <;>
      simpa only [characterDoubleShell,Fin.append_left,Fin.append_right] using hE a
  exact hd _

theorem scheduled_sourcePrimeShells_subset {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (E : Fin (sourceHalfSize cfg m) → Finset (PrimeUpTo Q)) (G : Finset (PrimeUpTo Q))
    (hE : ∀ i,E i⊆G) (i : (schedule k j).Constituent (sourceWidth cfg m)) :
    scheduledPrimeShells k (sourceWidth cfg m) (sourcePrimeShells cfg m E) j i⊆G := by
  rw [scheduledPrimeShells_eq_origin]
  exact sourcePrimeShells_subset cfg m E G hE _

theorem configuration_chosenPrime_shell {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (hm : 1 ≤ m) (hw : 0 < sourceWidth cfg m .word)
    (bulk top E : Finset (PrimeUpTo Q)) (v : WordSlot k j) :
    scheduledPrimeShells k (sourceWidth cfg m) (configurationPrimeShells cfg m bulk top E) j
      (chosenPrimeIndex k j (sourceWidth cfg m) hw v) = bulk := by
  change scheduledPrimeShells k (sourceWidth cfg m) (configurationPrimeShells cfg m bulk top E) j
    ⟨v.val,⟨0,by simpa only [v.property.2] using hw⟩⟩ = bulk
  rw [scheduledPrimeShells_word cfg m j bulk top E v.val v.property.2]
  change roleShells bulk top m (Fin.castAdd 1 ⟨0,by omega⟩) = bulk
  exact Fin.append_left _ _ _

section Actual
variable {d : Decomposition} {E : Finset ℕ} {δ L : ℝ} {k : ℕ} {α β ρ γ c₀ c BD : ℝ}
variable {s : SelectedWordSource d E δ L k α β ρ γ c₀}
variable (w : FixedConfigurationWitness s c BD)

theorem fixedConfiguration_chosenPrime_shell (hm : 1 ≤ wordSize k L)
    (hw : 0 < sourceWidth w.configuration (wordSize k L) .word) (j : ℕ) (v : WordSlot k j) :
    scheduledPrimeShells k (sourceWidth w.configuration (wordSize k L))
      (sourcePrimeShells w.configuration (wordSize k L) w.roles) j
      (chosenPrimeIndex k j (sourceWidth w.configuration (wordSize k L)) hw v) = s.locations.base 0 :=
  configuration_chosenPrime_shell w.configuration (wordSize k L) j hm hw
    (s.locations.base 0) (s.locations.base 2) s.locations.primes v

theorem fixedConfiguration_scheduled_unit_norm (j : ℕ)
    (i : (schedule k j).Constituent (sourceWidth w.configuration (wordSize k L)))
    (p : PrimeUpTo s.locations.Q) :
    ‖scheduledUnitData k (sourceWidth w.configuration (wordSize k L))
      (sourceUnitData w.configuration (wordSize k L) (fun _=>familyPhase s.family)) j i p‖ = 1 :=
  norm_scheduledUnitData k (sourceWidth w.configuration (wordSize k L)) _
    (fixedConfiguration_unit_norm w) j i p

theorem fixedConfiguration_scheduled_nonprincipal (j : ℕ)
    (i : (schedule k j).Constituent (sourceWidth w.configuration (wordSize k L)))
    (p : PrimeUpTo s.locations.Q)
    (hp : p∈scheduledPrimeShells k (sourceWidth w.configuration (wordSize k L))
      (sourcePrimeShells w.configuration (wordSize k L) w.roles) j i) :
    scheduledCharacterData k (sourceWidth w.configuration (wordSize k L))
      (sourceCharacterData w.configuration (wordSize k L) (fun _=>familyCharacter s.family)) j i p ≠ 1 :=
  scheduledCharacterData_nonprincipal k j (sourceWidth w.configuration (wordSize k L)) _ _
    (fixedConfiguration_character_nonprincipal w) i p hp

theorem fixedConfiguration_scheduled_shell_subset (j : ℕ)
    (i : (schedule k j).Constituent (sourceWidth w.configuration (wordSize k L))) :
    scheduledPrimeShells k (sourceWidth w.configuration (wordSize k L))
      (sourcePrimeShells w.configuration (wordSize k L) w.roles) j i⊆s.locations.primes :=
  scheduled_sourcePrimeShells_subset w.configuration (wordSize k L) j w.roles s.locations.primes
    w.roles_subset i

theorem fixedConfiguration_scheduled_log_bounds
    (hband : ∀ p∈E,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L)
    (j : ℕ) (i : (schedule k j).Constituent (sourceWidth w.configuration (wordSize k L)))
    (p : PrimeUpTo s.locations.Q)
    (hp : p∈scheduledPrimeShells k (sourceWidth w.configuration (wordSize k L))
      (sourcePrimeShells w.configuration (wordSize k L) w.roles) j i) :
    Real.exp (α*L) ≤ Real.log p.val ∧ Real.log p.val ≤ Real.exp (β*L) := by
  have hglobal := fixedConfiguration_scheduled_shell_subset w j i hp
  have he : p.val∈E := mem_boundedPrimeSet.mp hglobal
  have h := hband p.val he
  have hpos : 0 < Real.log p.val := Real.log_pos (by exact_mod_cast (primeUpTo_prime p).one_lt)
  have hl := Real.exp_le_exp.mpr h.1
  have hu := Real.exp_le_exp.mpr h.2
  rw [Real.exp_log hpos] at hl hu
  exact ⟨hl,hu⟩

end Actual
end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
