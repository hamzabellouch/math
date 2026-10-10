import Mathlib
import OAI.Computability.QuantumFactoring.FairOracle
import OAI.Computability.QuantumFactoring.TrialGuessLaw
import OAI.Computability.QuantumFactoring.OrderSamplerMass

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness

lemma parallelProgram_entry {p q : ℕ} (A : List (Instruction p)) (B : List (Instruction q))
    (x z : Basis p) (y u : Basis q) :
    (programMatrix (parallelProgram A B)).mulVec (basisVector (Fin.append x y)) (Fin.append z u)=
      ((programMatrix A).mulVec (basisVector x) z)*((programMatrix B).mulVec (basisVector y) u) := by
  rw [parallelProgram_basis]
  exact encodeState_at (appendEquiv p q) (appendEquiv p q).injective _ (z,u)

def productLayout {α β : Type*} {p q : ℕ} (e : α≃Basis p) (f : β≃Basis q) :
    α×β≃Basis (p+q) := (Equiv.prodCongr e f).trans (appendEquiv p q)
lemma productLayout_apply {α β : Type*} {p q : ℕ} (e : α≃Basis p) (f : β≃Basis q) (xy : α×β) :
    productLayout e f xy=Fin.append (e xy.1) (f xy.2) := rfl

namespace OrderTrial

abbrev guessWidth (n : ℕ) := n+(n+(n+retentionBits n))
def guessLayout (n : ℕ) : Guesses n≃Basis (guessWidth n) :=
  productLayout (Equiv.refl _) (productLayout (Equiv.refl _)
    (productLayout (Equiv.refl _) (Equiv.refl _)))
def guessProgram (n : ℕ) : List (Instruction (guessWidth n)) :=
  parallelProgram (hadamardPrefix n n le_rfl) (parallelProgram (hadamardPrefix n n le_rfl)
    (parallelProgram (hadamardPrefix n n le_rfl) (hadamardPrefix (retentionBits n) (retentionBits n) le_rfl)))
def guessZero (n : ℕ) : Guesses n := ((fun _ => false),(fun _ => false),(fun _ => false),(fun _ => false))

lemma guessProgram_entry (n : ℕ) (x : Guesses n) :
    (programMatrix (guessProgram n)).mulVec (basisVector (guessLayout n (guessZero n)))
      (guessLayout n x)=guessState n x := by
  simp only [guessProgram,guessLayout,productLayout_apply,guessZero,Equiv.refl_apply,
    parallelProgram_entry,hadamards_zero]
  rfl
lemma guessProgram_length (n : ℕ) : (guessProgram n).length=3*n+retentionBits n := by
  simp only [guessProgram,parallelProgram_length,hadamardPrefix_length]
  omega

abbrev Raw (w s n : ℕ) := Basis 2 × (Basis (OrderSample.width w (s+2)) × Guesses n)
abbrev rawWidth (w s n : ℕ) := 2+(OrderSample.width w (s+2)+guessWidth n)
def rawLayout (w s n : ℕ) : Raw w s n≃Basis (rawWidth w s n) :=
  productLayout (Equiv.refl _) (productLayout (Equiv.refl _) (guessLayout n))
def rawProgram (w s n : ℕ) : List (Instruction (rawWidth w s n)) :=
  parallelProgram (hadamardPrefix 2 2 le_rfl)
    (parallelProgram (OrderSample.completeSampler w s) (guessProgram n))
noncomputable def rawZero {w : ℕ} (s n : ℕ) (a m : Basis w) : Raw w s n :=
  ((fun _ => false),OrderSample.word a m (fun _ => false) (fun _ => false),guessZero n)
noncomputable def rawState {w : ℕ} (s n : ℕ) (a m : Basis w) : Raw w s n→ℂ :=
  independentState (fairState 2) (independentState (samplerState (s:=s) a m) (guessState n))

lemma rawProgram_entry {w : ℕ} (s n : ℕ) (a m : Basis w) (x : Raw w s n) :
    (programMatrix (rawProgram w s n)).mulVec (basisVector (rawLayout w s n (rawZero s n a m)))
      (rawLayout w s n x)=rawState s n a m x := by
  simp only [rawProgram,rawLayout,productLayout_apply,rawZero,Equiv.refl_apply,
    parallelProgram_entry,hadamards_zero,guessProgram_entry]
  rfl

lemma rawProgram_state {w : ℕ} (s n : ℕ) (a m : Basis w) :
    (programMatrix (rawProgram w s n)).mulVec (basisVector (rawLayout w s n (rawZero s n a m)))=
      encodeState (rawLayout w s n) (rawState s n a m) := by
  funext x
  obtain ⟨y,rfl⟩ := (rawLayout w s n).surjective x
  rw [rawProgram_entry,encodeState_at _ (rawLayout w s n).injective]

lemma raw_normalized {w : ℕ} (s n : ℕ) (a m : Basis w) :
    ∑ x, Complex.normSq (rawState s n a m x)=1 := by
  have h := RecordedHistory.append_normalized (samplerState (s:=s) a m) (fun _ => guessState n)
    (basis_preparation_normalized (OrderSample.completeSampler w s) _) (fun _ => guess_normalized n)
  exact RecordedHistory.append_normalized (fairState 2)
    (fun _ => independentState (samplerState (s:=s) a m) (guessState n))
    (fair_normalized 2) (fun _ => h)

/-- A physical Born event equals the corresponding retained-history event.
This layout is bijective; no outcome amplitudes are discarded. -/
lemma rawProgram_mass {w : ℕ} (s n : ℕ) (a m : Basis w) (P : Raw w s n→Prop) :
    outcomeMass (P ∘ (rawLayout w s n).symm)
      ((programMatrix (rawProgram w s n)).mulVec (basisVector (rawLayout w s n (rawZero s n a m))))=
      outcomeMass P (rawState s n a m) := by
  rw [rawProgram_state,outcomeMass_encode _ (rawLayout w s n).injective]
  congr 1
  funext x
  simp

end OrderTrial
end ExactQuantumFactoring


end

end OAI
