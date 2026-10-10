import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceFamily
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceWordDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSourceWord
open Construction Preliminaries

def roleShells {Q : ℕ} (bulk top : Finset (PrimeUpTo Q)) (m : ℕ) :
    Fin (m+1) → Finset (PrimeUpTo Q) :=
  Fin.append (fun _ : Fin m=>bulk) (fun _ : Fin 1=>top)

theorem roleShells_mass_pos {Q : ℕ} {bulk top : Finset (PrimeUpTo Q)}
    (hb : 0<primeShellMass bulk) (ht : 0<primeShellMass top) (m : ℕ) :
    ∀i,0<primeShellMass (roleShells bulk top m i) := by
  intro i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simpa only [roleShells,Fin.append_left] using hb
  · simpa only [roleShells,Fin.append_right] using ht

theorem rolePrior_eq {Q : ℕ} {bulk top : Finset (PrimeUpTo Q)}
    (hb : 0<primeShellMass bulk) (ht : 0<primeShellMass top) (m : ℕ) :
    rolePrior (primeShellPrior bulk hb) (primeShellPrior top ht) m =
      fun i=>primeShellPrior (roleShells bulk top m i) (roleShells_mass_pos hb ht m i) := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;>
    simp only [rolePrior,roleShells,Fin.append_left,Fin.append_right]

def binIndicator {Q m : ℕ} (J : ℤ) (w : Fin (m+1) → PrimeUpTo Q) : ℝ :=
  if ⌊wordLog w⌋=J then 1 else 0

theorem binIndicator_abs_le_one {Q m : ℕ} (J : ℤ) (w : Fin (m+1) → PrimeUpTo Q) :
    |binIndicator J w|≤1 := by unfold binIndicator; split_ifs <;> norm_num

theorem binMean_eq_initialCharacterMean {Q m : ℕ} {bulk top : Finset (PrimeUpTo Q)}
    (hb : 0<primeShellMass bulk) (ht : 0<primeShellMass top)
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (a : (q : ℕ) → ZMod q) (z : ℕ → ℂ)
    (J n : ℤ) :
    binMean (primeShellPrior bulk hb) (primeShellPrior top ht) m
      (fun p n=>phasedCharacter (χ p.val) (a p.val) (z p.val) (n:ZMod p.val)) J n =
    initialCharacterMean (roleShells bulk top m) (roleShells_mass_pos hb ht m)
      (fun _=>χ) (fun _=>a) (fun _=>z) (binIndicator J) n := by
  unfold binMean initialCharacterMean characterTuplePrior
  rw [rolePrior_eq hb ht m]
  congr 1
  funext w
  unfold binIndicator characterTupleTest
  split_ifs <;> simp

def familyCharacter {d : Decomposition} {Q : ℕ} {E : Finset (PrimeUpTo Q)} {δ : ℝ}
    (F : HigherBiasSourceFamily d Q E δ) (p : ℕ) : MulChar (ZMod p) ℂ :=
  if hp : p∈Q.primesLE then F.character ⟨p,hp⟩ else 1

def familyCenter {d : Decomposition} {Q : ℕ} {E : Finset (PrimeUpTo Q)} {δ : ℝ}
    (F : HigherBiasSourceFamily d Q E δ) (p : ℕ) : ZMod p :=
  if hp : p∈Q.primesLE then F.center ⟨p,hp⟩ else 0

def familyPhase {d : Decomposition} {Q : ℕ} {E : Finset (PrimeUpTo Q)} {δ : ℝ}
    (F : HigherBiasSourceFamily d Q E δ) (p : ℕ) : ℂ :=
  if hp : p∈Q.primesLE then F.phase ⟨p,hp⟩ else 1

@[simp] theorem family_phasedCharacter {d : Decomposition} {Q : ℕ}
    {E : Finset (PrimeUpTo Q)} {δ : ℝ} (F : HigherBiasSourceFamily d Q E δ)
    (p : PrimeUpTo Q) (x : ZMod p.val) :
    phasedCharacter (familyCharacter F p.val) (familyCenter F p.val) (familyPhase F p.val) x=
      F.test p x := by
  simp only [familyCharacter,familyCenter,familyPhase,p.property,dite_true,
    phasedCharacter,HigherBiasSourceFamily.test]

theorem familyPhase_norm {d : Decomposition} {Q : ℕ} {E : Finset (PrimeUpTo Q)} {δ : ℝ}
    (F : HigherBiasSourceFamily d Q E δ) (p : ℕ) : ‖familyPhase F p‖=1 := by
  unfold familyPhase
  split_ifs with hp
  · exact F.phase_unit _
  · norm_num

theorem family_binMean_eq_initialCharacterMean {d : Decomposition} {Q m : ℕ}
    {E bulk top : Finset (PrimeUpTo Q)} {δ : ℝ} (F : HigherBiasSourceFamily d Q E δ)
    (hb : 0<primeShellMass bulk) (ht : 0<primeShellMass top) (J n : ℤ) :
    binMean (primeShellPrior bulk hb) (primeShellPrior top ht) m
      (fun p n=>F.test p (n:ZMod p.val)) J n =
    initialCharacterMean (roleShells bulk top m) (roleShells_mass_pos hb ht m)
      (fun _=>familyCharacter F) (fun _=>familyCenter F) (fun _=>familyPhase F)
      (binIndicator J) n := by
  simpa only [family_phasedCharacter] using
    binMean_eq_initialCharacterMean (m:=m) hb ht (familyCharacter F) (familyCenter F) (familyPhase F) J n

end Ostmann.Characters.HigherBiasSourceWord

end

end OAI
