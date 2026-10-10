import Mathlib
import OAI.Analysis.MatrixSigning.Realization.CleanRoutine
import OAI.Analysis.MatrixSigning.Arithmetic.FloorRationalMachine

namespace OAI

namespace CurrentKS.FloorCleanRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine KS.W20.FloorRationalMachine

abbrev encode := KS.W01.encodeRat

def extract : Program 11 := CleanRoutine.transfer 5 10 0
def cleanProgram : Program 11 := compose program extract
lemma extract_spec (q : ℚ) : RunSpec extract (state [] (encode q)) (io (encode q))
    (2*(encode q).length+2) := by
  have h := CleanRoutine.transfer_spec (5 : Fin 11) 10 0 (by decide) (by decide) (by decide)
    (state [] (encode q)) rfl rfl
  convert h using 1 <;> (try rfl)
  funext j;fin_cases j <;> simp [state,KS.W19.SignedFloorMachine.«stacks»,io,Function.update]

def ticks (q : ℚ) : ℕ := KS.W29.polynomialFuel 64 2 (encode q).length+
  (2*(encode (⌊q⌋ : ℚ)).length+2)

def routine : Routine encode (fun q => encode (⌊q⌋ : ℚ)) ticks where
  scratch := 10
  program := cleanProgram
  spec q := by
    have h := (polynomial_spec q).compose (extract_spec (⌊q⌋ : ℚ))
    have hi : state (encode q) []=(@io 10 (encode q)) := by
      funext j;fin_cases j <;> rfl
    simp only [hi] at h
    exact h

end CurrentKS.FloorCleanRoutine

end OAI
