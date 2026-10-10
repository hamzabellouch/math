import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalMultiplicationMachine
import OAI.Analysis.MatrixSigning.Arithmetic.RationalReciprocalMachine
import OAI.Analysis.MatrixSigning.Encoding.WireProgramPrimitives

namespace OAI

namespace KS.W30.RationalDivision
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def corePorts : Fin 13 ↪ Fin 15 :=
  ⟨fun i => ⟨i.val, by omega⟩, by intro i j h; exact Fin.ext (congrArg (fun j : Fin 15=>j.val) h)⟩
def «stacks» (c : Fin 13 → List Bool) (den num : List Bool) : Fin 15 → List Bool :=
  ![c 0,c 1,c 2,c 3,c 4,c 5,c 6,c 7,c 8,c 9,c 10,c 11,c 12,den,num]
def liftCore (P : Program 13) : Program 15 := KS.W29.FixedSequential.liftPorts P corePorts

private theorem stacks_core (c : Fin 13→List Bool) (den num : List Bool) (i : Fin 13) :
    «stacks» c den num (corePorts i)=c i :=by
  fin_cases i <;> rfl

private theorem stacks_spare_value (c : Fin 13→List Bool) (den num : List Bool)
    (j : Fin 15) (hj : 13≤j.val) :
    «stacks» c den num j=(if j=(13 : Fin 15) then den else num) :=by
  have h : j.val=13 ∨ j.val=14 :=by omega
  rcases h with h | h
  · have he : j=(13 : Fin 15) :=Fin.ext h
    rw [he]
    simp [«stacks»]
  · have he : j=(14 : Fin 15) :=Fin.ext h
    rw [he]
    simp [«stacks»]

private theorem stacks_spare (before after : Fin 13→List Bool) (den num : List Bool)
    (j : Fin 15) (hj : ∀i,j≠corePorts i) :
    «stacks» after den num j=«stacks» before den num j :=by
  have hb : 13≤j.val :=by
    by_contra h
    have hi : j.val<13 :=by omega
    exact hj ⟨j.val,hi⟩ (Fin.ext rfl)
  rw [stacks_spare_value _ _ _ _ hb,stacks_spare_value _ _ _ _ hb]

theorem liftCore_spec (P : Program 13) (before after : Fin 13 → List Bool)
    (den num : List Bool) (ticks : ℕ) (h : RunSpec P before after ticks) :
    RunSpec (liftCore P) («stacks» before den num) («stacks» after den num) ticks :=
  KS.W01.FixedPortRunSpec.lift_runSpec P corePorts before after _ _ ticks h
    (stacks_core before den num) (stacks_core after den num) (stacks_spare before after den num)

def parseNumerator : Program 15 := liftCore KS.W06.SingleRationalParser.program
def storeDenominator : Program 15 := KS.W15.WireProgram.transferProgram 0 13 8
def serializeNumerator : Program 15 := liftCore KS.W01.SignedRationalSerializer.program
def storeNumerator : Program 15 := KS.W15.WireProgram.transferProgram 10 14 8
def restoreDenominator : Program 15 := KS.W15.WireProgram.transferProgram 13 0 8
def reciprocal : Program 15 := liftCore RationalReciprocal.program
def prepareInverse : Program 15 := KS.W15.WireProgram.transferProgram 10 0 8
def prependNumerator : Program 15 := KS.W15.WireProgram.transferProgram 14 0 8
def multiply : Program 15 := liftCore KS.W15.RationalMultiply.program

def inputBits (q r : ℚ) : List Bool := KS.W01.encodeRat q ++ KS.W01.encodeRat r

def inputState (wire : List Bool) : Fin 15 → List Bool :=
  «stacks» (RationalReciprocal.inputState wire) [] []
def outputState (wire : List Bool) : Fin 15 → List Bool :=
  «stacks» (RationalReciprocal.outputState wire) [] []

theorem parseNumerator_spec (q r : ℚ) :
    RunSpec parseNumerator (inputState (inputBits q r))
      («stacks» (KS.W06.SingleRationalParser.canonicalState q (KS.W01.encodeRat r)) [] [])
      (8 * (KS.W01.ratLength q + 1)) :=
  liftCore_spec _ _ _ [] [] _ (KS.W06.SingleRationalParser.canonical_spec q (KS.W01.encodeRat r))

theorem storeDenominator_spec (q r : ℚ) :
    RunSpec storeDenominator
      («stacks» (KS.W06.SingleRationalParser.canonicalState q (KS.W01.encodeRat r)) [] [])
      («stacks» (RationalReciprocal.canonicalState q) (KS.W01.encodeRat r) [])
      (2 * KS.W01.ratLength r + 2) := by
  have h := KS.W15.WireProgram.transfer_spec (0 : Fin 15) 13 8 (by decide) (by decide) (by decide)
    («stacks» (KS.W06.SingleRationalParser.canonicalState q (KS.W01.encodeRat r)) [] []) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;>
    simp [KS.W15.WireProgram.transferAfter, «stacks»,
      RationalReciprocal.canonicalState, RationalMagnitudeMachine.state,
      RationalMagnitudeMachine.«stacks»,
      KS.W06.SingleRationalParser.canonicalState, KS.W06.SingleRationalParser.state])

def serializerTicks (q : ℚ) : ℕ :=
  16 * ((Computability.encodeNat q.num.natAbs).length + (Computability.encodeNat q.den).length + 1)

theorem serializeNumerator_spec (q r : ℚ) :
    RunSpec serializeNumerator
      («stacks» (RationalReciprocal.canonicalState q) (KS.W01.encodeRat r) [])
      («stacks» (RationalReciprocal.outputState (KS.W01.encodeRat q)) (KS.W01.encodeRat r) [])
      (serializerTicks q) :=
  liftCore_spec _ _ _ _ [] _ (KS.W01.SignedRationalSerializer.serializes_rational q)

theorem storeNumerator_spec (q r : ℚ) :
    RunSpec storeNumerator
      («stacks» (RationalReciprocal.outputState (KS.W01.encodeRat q)) (KS.W01.encodeRat r) [])
      («stacks» (RationalReciprocal.inputState []) (KS.W01.encodeRat r) (KS.W01.encodeRat q))
      (2 * KS.W01.ratLength q + 2) := by
  have h := KS.W15.WireProgram.transfer_spec (10 : Fin 15) 14 8 (by decide) (by decide) (by decide)
    («stacks» (RationalReciprocal.outputState (KS.W01.encodeRat q)) (KS.W01.encodeRat r) []) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;>
    simp [KS.W15.WireProgram.transferAfter, «stacks»,
      RationalReciprocal.inputState, RationalReciprocal.outputState,
      KS.W06.SingleRationalParser.inputState, KS.W01.SignedRationalSerializer.outputState])

theorem restoreDenominator_spec (q r : ℚ) :
    RunSpec restoreDenominator
      («stacks» (RationalReciprocal.inputState []) (KS.W01.encodeRat r) (KS.W01.encodeRat q))
      («stacks» (RationalReciprocal.inputState (KS.W01.encodeRat r)) [] (KS.W01.encodeRat q))
      (2 * KS.W01.ratLength r + 2) := by
  have h := KS.W15.WireProgram.transfer_spec (13 : Fin 15) 0 8 (by decide) (by decide) (by decide)
    («stacks» (RationalReciprocal.inputState []) (KS.W01.encodeRat r) (KS.W01.encodeRat q)) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;>
    simp [KS.W15.WireProgram.transferAfter, «stacks»,
      RationalReciprocal.inputState, KS.W06.SingleRationalParser.inputState])

theorem reciprocal_spec (q r : ℚ) :
    RunSpec reciprocal
      («stacks» (RationalReciprocal.inputState (KS.W01.encodeRat r)) [] (KS.W01.encodeRat q))
      («stacks» (RationalReciprocal.outputState (KS.W01.encodeRat r⁻¹)) [] (KS.W01.encodeRat q))
      (1000 * (KS.W01.ratLength r + 1) ^ 3) :=
  liftCore_spec _ _ _ [] _ _ (RationalReciprocal.program_spec r)

theorem prepareInverse_spec (q r : ℚ) :
    RunSpec prepareInverse
      («stacks» (RationalReciprocal.outputState (KS.W01.encodeRat r⁻¹)) [] (KS.W01.encodeRat q))
      («stacks» (RationalReciprocal.inputState (KS.W01.encodeRat r⁻¹)) [] (KS.W01.encodeRat q))
      (2 * KS.W01.ratLength r⁻¹ + 2) := by
  have h := KS.W15.WireProgram.transfer_spec (10 : Fin 15) 0 8 (by decide) (by decide) (by decide)
    («stacks» (RationalReciprocal.outputState (KS.W01.encodeRat r⁻¹)) [] (KS.W01.encodeRat q)) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;>
    simp [KS.W15.WireProgram.transferAfter, «stacks»,
      RationalReciprocal.inputState, RationalReciprocal.outputState,
      KS.W06.SingleRationalParser.inputState, KS.W01.SignedRationalSerializer.outputState])

theorem prependNumerator_spec (q r : ℚ) :
    RunSpec prependNumerator
      («stacks» (RationalReciprocal.inputState (KS.W01.encodeRat r⁻¹)) [] (KS.W01.encodeRat q))
      (inputState (inputBits q r⁻¹)) (2 * KS.W01.ratLength q + 2) := by
  have h := KS.W15.WireProgram.transfer_spec (14 : Fin 15) 0 8 (by decide) (by decide) (by decide)
    («stacks» (RationalReciprocal.inputState (KS.W01.encodeRat r⁻¹)) [] (KS.W01.encodeRat q)) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;>
    simp [KS.W15.WireProgram.transferAfter, «stacks», inputState, inputBits,
      RationalReciprocal.inputState, KS.W06.SingleRationalParser.inputState])

theorem multiply_spec (q r : ℚ) :
    RunSpec multiply (inputState (inputBits q r⁻¹))
      (outputState (KS.W01.encodeRat (q / r))) (KS.W15.RationalMultiply.totalTicks q r⁻¹) := by
  simp only [div_eq_mul_inv]
  exact liftCore_spec _ _ _ [] [] _ (KS.W15.RationalMultiply.full_spec q r⁻¹)

end KS.W30.RationalDivision

end OAI
