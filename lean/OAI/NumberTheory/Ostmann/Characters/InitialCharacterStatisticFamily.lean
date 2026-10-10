import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceFamily
import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticLower
import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticRoles

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters
open Construction Preliminaries
namespace HigherBiasSourceFamily
variable {d : Decomposition} {Q : ℕ} {E : Finset (PrimeUpTo Q)} {δ : ℝ}

def characterNat (F : HigherBiasSourceFamily d Q E δ) (q : ℕ) : MulChar (ZMod q) ℂ :=
  if hq : q ∈ Q.primesLE then F.character ⟨q,hq⟩ else 1

def centerNat (F : HigherBiasSourceFamily d Q E δ) (q : ℕ) : ZMod q :=
  if hq : q ∈ Q.primesLE then F.center ⟨q,hq⟩ else 0

def phaseNat (F : HigherBiasSourceFamily d Q E δ) (q : ℕ) : ℂ :=
  if hq : q ∈ Q.primesLE then F.phase ⟨q,hq⟩ else 1

@[simp] theorem characterNat_coe (F : HigherBiasSourceFamily d Q E δ) (p : PrimeUpTo Q) :
    F.characterNat p.val = F.character p := by simp only [characterNat, dite_eq_left p.property]

@[simp] theorem centerNat_coe (F : HigherBiasSourceFamily d Q E δ) (p : PrimeUpTo Q) :
    F.centerNat p.val = F.center p := by simp only [centerNat, dite_eq_left p.property]

@[simp] theorem phaseNat_coe (F : HigherBiasSourceFamily d Q E δ) (p : PrimeUpTo Q) :
    F.phaseNat p.val = F.phase p := by simp only [phaseNat, dite_eq_left p.property]

theorem characterNat_nonprincipal (F : HigherBiasSourceFamily d Q E δ)
    {p : PrimeUpTo Q} (hp : p ∈ E) : F.characterNat p.val ≠ 1 := by
  rw [characterNat_coe]
  intro he
  have hh := F.higher_order p hp
  rw [he, orderOf_one] at hh
  omega

theorem phaseNat_norm (F : HigherBiasSourceFamily d Q E δ) (p : PrimeUpTo Q) :
    ‖F.phaseNat p.val‖ = 1 := by rw [phaseNat_coe, F.phase_unit]

@[simp] theorem phasedCharacter_nat_eq_test (F : HigherBiasSourceFamily d Q E δ)
    (p : PrimeUpTo Q) (x : ZMod p.val) :
    phasedCharacter (F.characterNat p.val) (F.centerNat p.val) (F.phaseNat p.val) x = F.test p x := by
  simp only [phasedCharacter, characterNat_coe, centerNat_coe, phaseNat_coe, test]

theorem initialCharacterMean_eq_original (F : HigherBiasSourceFamily d Q E δ)
    {b : ℕ} (G : Fin b → Finset (PrimeUpTo Q)) (hG : ∀ i, 0 < primeShellMass (G i))
    (B : (Fin b → PrimeUpTo Q) → ℝ) (n : ℤ) :
    initialCharacterMean G hG (fun _ => F.characterNat) (fun _ => F.centerNat)
      (fun _ => F.phaseNat) B n =
      (characterTuplePrior G hG).cmean (fun w => (B w : ℂ)*∏ i, F.test (w i) (n : ZMod (w i).val)) := by
  unfold initialCharacterMean characterTupleTest
  simp only [phasedCharacter_nat_eq_test]

theorem initialCharacterSource_inputs (F : HigherBiasSourceFamily d Q E δ)
    {b : ℕ} (G : Fin b → Finset (PrimeUpTo Q)) (hG : ∀ i, G i ⊆ E) :
    (∀ i, ∀ p ∈ G i, F.characterNat p.val ≠ 1) ∧
    (∀ i, ∀ p ∈ G i, ‖F.phaseNat p.val‖ ≤ 1) :=
  ⟨fun i p hp => F.characterNat_nonprincipal (p := p) (hG i hp), fun _ p _ => (F.phaseNat_norm p).le⟩

end HigherBiasSourceFamily
end Ostmann.Characters

end

end OAI
