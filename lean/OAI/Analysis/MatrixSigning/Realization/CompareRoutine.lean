import Mathlib
import OAI.Analysis.MatrixSigning.Realization.PairRoutine
import OAI.Analysis.MatrixSigning.Arithmetic.CleanRationalCompare

namespace OAI

namespace CurrentKS.CompareRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine KS.W04.CleanRationalCompare

abbrev encode := KS.W01.encodeRat

def parsed (q r : ℚ) : Fin 13 → Word :=
  fun j => if j=0 then encode r else if j=11 then encode q else []
def decode : Program 13 := KS.W11.FrameWireCodec.unframeProgram ⟨![0,11,12],by decide⟩
def prepend : Program 13 := KS.W12.StackTransfer.program 11 0 12
def extract : Program 13 := CleanRoutine.transfer 9 12 0
def program : Program 13 := compose decode (compose prepend (compose cleanedComparator extract))

lemma decode_spec (q r : ℚ) : RunSpec decode (io (PairRoutine.pair (encode q) (encode r)))
    (parsed q r) (3*(encode q).length+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec (⟨![0,11,12],by decide⟩ : Fin 3 ↪ Fin 13)
    (fun _ => []) (encode q) (encode r)
  convert h using 1 <;> (try rfl) <;> funext j <;> fin_cases j <;> rfl
lemma prepend_spec (q r : ℚ) : RunSpec prepend (parsed q r) (inputState q r)
    (2*(encode q).length+2) := by
  have h := KS.W12.StackTransfer.spec (11 : Fin 13) 0 12 (by decide) (by decide) (by decide)
    (parsed q r) rfl
  convert h using 1 <;> (try rfl)
  funext j;fin_cases j <;> simp [parsed,inputState,KS.W06.RationalCompare.fields,KS.W12.StackTransfer.after]
lemma extract_spec (b : Bool) : RunSpec extract (flagState b) (io [b]) 4 := by
  have h := CleanRoutine.transfer_spec (9 : Fin 13) 12 0 (by decide) (by decide) (by decide)
    (flagState b) rfl rfl
  convert h using 1 <;> (try rfl)
  funext j;fin_cases j <;> simp [flagState,io,Function.update]

def ticks (q r : ℚ) : ℕ :=
  (3*(encode q).length+2)+(2*(encode q).length+2)+
    KS.W29.polynomialFuel 2048 2 (encode q++encode r).length+4

def routine : Routine (fun p : ℚ×ℚ => PairRoutine.pair (encode p.1) (encode p.2))
    (fun p => [decide (p.1≤p.2)]) (fun p => ticks p.1 p.2) where
  scratch := 12
  program := program
  spec p := by
    have h := (decode_spec p.1 p.2).compose ((prepend_spec p.1 p.2).compose
      ((cleaned_polynomial_spec p.1 p.2).compose (extract_spec (decide (p.1≤p.2)))))
    simp only [ticks,Nat.add_assoc] at h ⊢
    exact h

end CurrentKS.CompareRoutine

end OAI
