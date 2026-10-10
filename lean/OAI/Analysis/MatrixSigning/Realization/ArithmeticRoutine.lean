import Mathlib
import OAI.Analysis.MatrixSigning.Realization.PairRoutine
import OAI.Analysis.MatrixSigning.Machines.ExpressionPrimitives

namespace OAI

namespace CurrentKS.ArithmeticRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine PairRoutine
open KS.W13.ExpressionMachine

abbrev encode := KS.W01.encodeRat

def decodeLeft : Program 24 :=
  KS.W11.FrameWireCodec.unframeProgram ⟨![0,23,22],by decide⟩
def program (op : BinaryOp) : Program 24 :=
  compose decodeLeft (compose leftPrepend
    (compose (binaryArithmetic op) (CleanRoutine.transfer 10 19 0)))

lemma decode_spec (q r : ℚ) :
    RunSpec decodeLeft (io (pair (encode q) (encode r)))
      (registers [] [] (encode r) [] (encode q) []) (3*(encode q).length+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec
    (⟨![0,23,22],by decide⟩ : Fin 3 ↪ Fin 24) (fun _ => []) (encode q) (encode r)
  convert h using 1 <;> (try rfl) <;> funext j <;> fin_cases j <;> rfl

lemma prepend_spec (q r : ℚ) :
    RunSpec leftPrepend (registers [] [] (encode r) [] (encode q) [])
      (registers [] [] (encode q++encode r) [] [] []) (2*(encode q).length+2) := by
  have h := KS.W12.StackTransfer.spec (23 : Fin 24) 0 22 (by decide) (by decide) (by decide)
    (registers [] [] (encode r) [] (encode q) []) rfl
  convert h using 1 <;> (try rfl)
  funext j;fin_cases j <;> simp [registers,KS.W12.StackTransfer.after]

lemma extract_spec (q : ℚ) :
    RunSpec (CleanRoutine.transfer (10 : Fin 24) 19 0)
      (registers [] [] [] (encode q) [] []) (io (encode q)) (2*(encode q).length+2) := by
  have h := CleanRoutine.transfer_spec (10 : Fin 24) 19 0 (by decide) (by decide) (by decide)
    (registers [] [] [] (encode q) [] []) rfl rfl
  convert h using 1 <;> (try rfl)
  funext j;fin_cases j <;> simp [registers,io,Function.update]

def ticks (op : BinaryOp) (q r : ℚ) : ℕ :=
  (3*(encode q).length+2)+(2*(encode q).length+2)+binaryBudget q r+
    (2*(encode (op.eval q r)).length+2)

lemma program_spec (op : BinaryOp) (q r : ℚ) :
    RunSpec (program op) (io (pair (encode q) (encode r)))
      (io (encode (op.eval q r))) (ticks op q r) := by
  have h := (decode_spec q r).compose ((prepend_spec q r).compose
    ((binaryArithmetic_spec op q r [] []).compose (extract_spec (op.eval q r))))
  simp only [ticks,Nat.add_assoc] at h ⊢
  exact h

def routine (op : BinaryOp) :
    Routine (fun p : ℚ×ℚ => pair (encode p.1) (encode p.2))
      (fun p => encode (op.eval p.1 p.2)) (fun p => ticks op p.1 p.2) where
  scratch := 23
  program := program op
  spec p := program_spec op p.1 p.2

end CurrentKS.ArithmeticRoutine

end OAI
