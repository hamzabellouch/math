import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.FrameWireCodec
import OAI.Analysis.MatrixSigning.Machines.ExpressionSyntax
import OAI.Analysis.MatrixSigning.Arithmetic.RationalSubtractCorrect
import OAI.Analysis.MatrixSigning.Arithmetic.RationalDivisionMachine

namespace OAI

section

namespace KS.W13.ExpressionMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def registers (source values input output left sign : List Bool) : Fin 24 → List Bool :=
  fun j => if j=20 then source else if j=21 then values else if j=0 then input
    else if j=10 then output else if j=23 then left else if j=13 then sign else []
def boundary (source : List Bool) (s : List ℚ) : Fin 24 → List Bool :=
  registers source (encodeStack s) [] [] [] []

def firstPorts (n : ℕ) (hn : n ≤ 24) : Fin n ↪ Fin 24 :=
  ⟨fun i => ⟨i.val,lt_of_lt_of_le i.isLt hn⟩,fun _ _ h => Fin.ext (congrArg (fun j : Fin 24 => j.val) h)⟩

def leafPorts : Fin 3 ↪ Fin 24 := ⟨![20,10,22],by decide⟩
def rightPorts : Fin 3 ↪ Fin 24 := ⟨![21,0,22],by decide⟩
def leftPorts : Fin 3 ↪ Fin 24 := ⟨![21,23,22],by decide⟩
def framePorts : Fin 3 ↪ Fin 24 := ⟨![0,10,22],by decide⟩
def finalPorts : Fin 3 ↪ Fin 24 := ⟨![21,10,22],by decide⟩
def leafDecode : Program 24 := KS.W11.FrameWireCodec.unframeProgram leafPorts
def rightDecode : Program 24 := KS.W11.FrameWireCodec.unframeProgram rightPorts
def leftDecode : Program 24 := KS.W11.FrameWireCodec.unframeProgram leftPorts
def resultFrame : Program 24 := KS.W11.FrameWireCodec.frameProgram framePorts
def resultPush : Program 24 := KS.W12.StackTransfer.program 10 21 22
def leftPrepend : Program 24 := KS.W12.StackTransfer.program 23 0 22

theorem leafDecode_spec (q : ℚ) (source : List Bool) (s : List ℚ) :
    RunSpec leafDecode (boundary (KS.W01.frame (KS.W01.encodeRat q) ++ source) s)
      (registers source (encodeStack s) [] (KS.W01.encodeRat q) [] [])
      (3*KS.W01.ratLength q+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec leafPorts (boundary source s) (KS.W01.encodeRat q) source
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)

theorem rightDecode_spec (q : ℚ) (source : List Bool) (s : List ℚ) :
    RunSpec rightDecode (boundary source (q::s))
      (registers source (encodeStack s) (KS.W01.encodeRat q) [] [] [])
      (3*KS.W01.ratLength q+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec rightPorts (boundary source s) (KS.W01.encodeRat q) (encodeStack s)
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)

theorem leftDecode_spec (q r : ℚ) (source : List Bool) (s : List ℚ) :
    RunSpec leftDecode (registers source (encodeStack (q::s)) (KS.W01.encodeRat r) [] [] [])
      (registers source (encodeStack s) (KS.W01.encodeRat r) [] (KS.W01.encodeRat q) [])
      (3*KS.W01.ratLength q+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec leftPorts
    (registers source (encodeStack s) (KS.W01.encodeRat r) [] [] []) (KS.W01.encodeRat q) (encodeStack s)
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)

theorem leftPrepend_spec (q r : ℚ) (source : List Bool) (s : List ℚ) :
    RunSpec leftPrepend (registers source (encodeStack s) (KS.W01.encodeRat r) [] (KS.W01.encodeRat q) [])
      (registers source (encodeStack s) (KS.W01.encodeRat q++KS.W01.encodeRat r) [] [] [])
      (2*KS.W01.ratLength q+2) := by
  have h := KS.W12.StackTransfer.spec (23 : Fin 24) 0 22 (by decide) (by decide) (by decide)
    (registers source (encodeStack s) (KS.W01.encodeRat r) [] (KS.W01.encodeRat q) []) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> simp [registers,KS.W12.StackTransfer.after])

theorem resultFrame_spec (q : ℚ) (source : List Bool) (s : List ℚ) :
    RunSpec resultFrame (registers source (encodeStack s) [] (KS.W01.encodeRat q) [] [])
      (registers source (encodeStack s) [] (KS.W01.frame (KS.W01.encodeRat q)) [] [])
      (4*KS.W01.ratLength q+3) := by
  have h := KS.W11.FrameWireCodec.frame_spec framePorts (boundary source s) (KS.W01.encodeRat q)
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)

theorem resultPush_spec (q : ℚ) (source : List Bool) (s : List ℚ) :
    RunSpec resultPush (registers source (encodeStack s) [] (KS.W01.frame (KS.W01.encodeRat q)) [] [])
      (boundary source (q::s)) (4*KS.W01.ratLength q+4) := by
  have h := KS.W12.StackTransfer.spec (10 : Fin 24) 21 22 (by decide) (by decide) (by decide)
    (registers source (encodeStack s) [] (KS.W01.frame (KS.W01.encodeRat q)) [] []) rfl
  convert h using 1 <;> first | rfl |
    (funext j; fin_cases j <;> simp [registers,boundary,encodeStack,KS.W12.StackTransfer.after]) |
    (simp [registers,KS.W01.ratLength,KS.W01.length_frame];omega)

def finishValue : Program 24 := compose resultFrame resultPush

theorem finishValue_spec (q : ℚ) (source : List Bool) (s : List ℚ) :
    RunSpec finishValue (registers source (encodeStack s) [] (KS.W01.encodeRat q) [] [])
      (boundary source (q::s)) (8*KS.W01.ratLength q+7) := by
  convert (resultFrame_spec q source s).compose (resultPush_spec q source s) using 1 <;> first | rfl | omega

inductive BinaryOp where | add | sub | mul | div deriving DecidableEq

def BinaryOp.eval : BinaryOp → ℚ → ℚ → ℚ
  | .add,q,r => q+r
  | .sub,q,r => q-r
  | .mul,q,r => q*r
  | .div,q,r => q/r

def binaryArithmetic : BinaryOp → Program 24
  | .add => KS.W29.FixedSequential.liftPorts KS.W13.RationalAdd.program (firstPorts 16 (by decide))
  | .sub => KS.W29.FixedSequential.liftPorts KS.W13.RationalSubtract.program (firstPorts 19 (by decide))
  | .mul => KS.W29.FixedSequential.liftPorts KS.W15.RationalMultiply.program (firstPorts 13 (by decide))
  | .div => KS.W29.FixedSequential.liftPorts KS.W30.RationalDivision.program (firstPorts 15 (by decide))

def binaryBudget (q r : ℚ) : ℕ := 2000000*(KS.W01.ratLength q+KS.W01.ratLength r+1)^3

theorem binaryArithmetic_spec (op : BinaryOp) (q r : ℚ) (source : List Bool) (s : List ℚ) :
    RunSpec (binaryArithmetic op) (registers source (encodeStack s) (KS.W01.encodeRat q++KS.W01.encodeRat r) [] [] [])
      (registers source (encodeStack s) [] (KS.W01.encodeRat (op.eval q r)) [] []) (binaryBudget q r) := by
  cases op
  · have hsmall := KS.W13.RationalAdd.polynomial_spec q r
    have hlarge : RunSpec (binaryArithmetic .add)
        (registers source (encodeStack s) (KS.W01.encodeRat q++KS.W01.encodeRat r) [] [] [])
        (registers source (encodeStack s) [] (KS.W01.encodeRat (BinaryOp.add.eval q r)) [] [])
        (KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) := by
      apply KS.W01.FixedPortRunSpec.lift_runSpec KS.W13.RationalAdd.program (firstPorts 16 (by decide)) _ _ _ _ _ hsmall
      · intro i; fin_cases i <;> rfl
      · intro i; fin_cases i <;> rfl
      · intro j hj
        have h0 : j ≠ 0 := hj 0
        have h10 : j ≠ 10 := hj 10
        simp [registers,h0,h10]
    apply hlarge.mono
    simp only [KS.W29.polynomialFuel,List.length_append]
    change _ * (KS.W01.ratLength q+KS.W01.ratLength r+1)^3 ≤ binaryBudget q r
    exact Nat.mul_le_mul_right _ (by decide)
  · have hsmall := KS.W13.RationalSubtract.polynomial_spec q r
    have hlarge : RunSpec (binaryArithmetic .sub)
        (registers source (encodeStack s) (KS.W01.encodeRat q++KS.W01.encodeRat r) [] [] [])
        (registers source (encodeStack s) [] (KS.W01.encodeRat (BinaryOp.sub.eval q r)) [] [])
        (KS.W29.polynomialFuel 600000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) := by
      apply KS.W01.FixedPortRunSpec.lift_runSpec KS.W13.RationalSubtract.program (firstPorts 19 (by decide)) _ _ _ _ _ hsmall
      · intro i; fin_cases i <;> rfl
      · intro i; fin_cases i <;> rfl
      · intro j hj
        have h0 : j ≠ 0 := hj 0
        have h10 : j ≠ 10 := hj 10
        simp [registers,h0,h10]
    apply hlarge.mono
    simp only [KS.W29.polynomialFuel,List.length_append]
    change _ * (KS.W01.ratLength q+KS.W01.ratLength r+1)^3 ≤ binaryBudget q r
    exact Nat.mul_le_mul_right _ (by decide)
  · have hsmall := (KS.W15.RationalMultiply.full_spec q r).mono (KS.W15.RationalMultiply.totalTicks_le_polynomial q r)
    have hlarge : RunSpec (binaryArithmetic .mul)
        (registers source (encodeStack s) (KS.W01.encodeRat q++KS.W01.encodeRat r) [] [] [])
        (registers source (encodeStack s) [] (KS.W01.encodeRat (BinaryOp.mul.eval q r)) [] [])
        (KS.W29.polynomialFuel 2048 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) := by
      apply KS.W01.FixedPortRunSpec.lift_runSpec KS.W15.RationalMultiply.program (firstPorts 13 (by decide)) _ _ _ _ _ hsmall
      · intro i; fin_cases i <;> rfl
      · intro i; fin_cases i <;> rfl
      · intro j hj
        have h0 : j ≠ 0 := hj 0
        have h10 : j ≠ 10 := hj 10
        simp [registers,h0,h10]
    apply hlarge.mono
    simp only [KS.W29.polynomialFuel,List.length_append]
    change _ * (KS.W01.ratLength q+KS.W01.ratLength r+1)^3 ≤ binaryBudget q r
    exact Nat.mul_le_mul_right _ (by decide)
  · have hsmall := KS.W30.RationalDivision.program_spec q r
    have hlarge : RunSpec (binaryArithmetic .div)
        (registers source (encodeStack s) (KS.W01.encodeRat q++KS.W01.encodeRat r) [] [] [])
        (registers source (encodeStack s) [] (KS.W01.encodeRat (BinaryOp.div.eval q r)) [] [])
        (KS.W29.polynomialFuel 1100000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) := by
      apply KS.W01.FixedPortRunSpec.lift_runSpec KS.W30.RationalDivision.program (firstPorts 15 (by decide)) _ _ _ _ _ hsmall
      · intro i; fin_cases i <;> rfl
      · intro i; fin_cases i <;> rfl
      · intro j hj
        have h0 : j ≠ 0 := hj 0
        have h10 : j ≠ 10 := hj 10
        simp [registers,h0,h10]
    apply hlarge.mono
    simp only [KS.W29.polynomialFuel,List.length_append]
    change _ * (KS.W01.ratLength q+KS.W01.ratLength r+1)^3 ≤ binaryBudget q r
    exact Nat.mul_le_mul_right _ (by decide)

end KS.W13.ExpressionMachine

end

end OAI
