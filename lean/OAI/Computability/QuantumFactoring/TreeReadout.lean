import Mathlib
import OAI.Computability.QuantumFactoring.TreeAmplified

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork BitArithmetic Exactness

/-- The readout is a clean reversible Boolean network, not a classical hidden
postprocessor. The preparation's complete history is retained. -/
def readoutProgram {q m r : ℕ} (P : List (Instruction q))
    (c : BooleanNetwork q m) (hr : c.net.count≤r) : List (Instruction (q+m+r)) :=
  firstProgram m r P++oracleOn c hr

lemma readoutProgram_state {q m r : ℕ} (P : List (Instruction q))
    (c : BooleanNetwork q m) (hr : c.net.count≤r) (z : Basis q) :
    (programMatrix (readoutProgram P c hr)).mulVec
      (basisVector (packed r z (fun _=>false)))=
      encodeState (fun x=>packed r x (c.eval x)) ((programMatrix P).mulVec (basisVector z)) := by
  rw [readoutProgram,programMatrix_append,←Matrix.mulVec_mulVec,firstProgram_basis]
  rw [encodeState,Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul,oracleOn_basis,Bool.false_xor]
  rfl

lemma readoutProgram_length {q m r : ℕ} (P : List (Instruction q))
    (c : BooleanNetwork q m) (hr : c.net.count≤r) :
    (readoutProgram P c hr).length≤P.length+4*c.net.count+2*m := by
  have hh:=oracleOn_length c hr
  simp only [readoutProgram,List.length_append,firstProgram_length]
  omega

namespace PhysicalTree
abbrev readoutWork (n : ℕ) (hn : 0<n) := (amplifiedOutput n hn).net.count
abbrev readoutWidth (n : ℕ) (hn : 0<n) := amplifiedWidth n hn+n*n+readoutWork n hn

def factoringProgram (n : ℕ) (hn : 0<n) : List (Instruction (readoutWidth n hn)) :=
  readoutProgram (amplifiedProgram n hn) (amplifiedOutput n hn) le_rfl
def factoringZero (n N : ℕ) (hn : 0<n) : Basis (readoutWidth n hn) :=
  packed (readoutWork n hn) (amplifiedZero n N hn) (fun _=>false)
def factoringResult (n : ℕ) (hn : 0<n) (x : Basis (readoutWidth n hn)) : Basis (n*n) :=
  x ∘ targetRegister (amplifiedWidth n hn) (n*n) (readoutWork n hn)

/-- Probability ONE of complete factorization for the actual finite physical
fixed-gate program, with its clean reversible readout. Polynomial resource
bounds and finite-alphabet polynomial-time uniformity are separate properties
of the same circuit family. -/
theorem factoringProgram_exact {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n) :
    outcomeMass (fun x=>CorrectEncoding N n (guessWords n (factoringResult n (by omega) x)))
      ((programMatrix (factoringProgram n (by omega))).mulVec
        (basisVector (factoringZero n N (by omega))))=1 := by
  rw [factoringProgram,factoringZero,readoutProgram_state]
  have hi : Function.Injective (fun x : Basis (amplifiedWidth n (by omega))=>
      packed (readoutWork n (by omega)) x ((amplifiedOutput n (by omega)).eval x)) := by
    intro x y hxy
    have hh:=congrArg (fun z=>z ∘ firstRegister (amplifiedWidth n (by omega)) (n*n)
      (readoutWork n (by omega))) hxy
    simpa only [packed_first] using hh
  rw [outcomeMass_encode _ hi]
  have he : ((fun x : Basis (readoutWidth n (by omega))=>CorrectEncoding N n (guessWords n (factoringResult n (by omega) x))) ∘
      (fun x : Basis (amplifiedWidth n (by omega))=>packed (readoutWork n (by omega)) x ((amplifiedOutput n (by omega)).eval x)))=
      (fun x : Basis (amplifiedWidth n (by omega))=>CorrectEncoding N n (guessWords n ((amplifiedOutput n (by omega)).eval x))) := by
    funext x
    simp only [Function.comp_apply,factoringResult,packed_targetRegister]
  rw [he]
  exact amplified_mass_one hn hN hb

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
