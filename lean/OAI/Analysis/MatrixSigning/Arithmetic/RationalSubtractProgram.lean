import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalAddCorrect
import OAI.Analysis.MatrixSigning.Arithmetic.RationalSignAction
import OAI.Analysis.MatrixSigning.Machines.FixedDotPrimitives

namespace OAI

namespace KS.W13.RationalSubtract
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def firstPorts (n : ℕ) (hn : n ≤ 19) : Fin n ↪ Fin 19 :=
  ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt hn⟩, fun _ _ h => Fin.ext (congrArg (fun j : Fin 19 => j.val) h)⟩

def extend {n : ℕ} (s : Fin n → List Bool) (spare : Fin 19 → List Bool) : Fin 19 → List Bool :=
  fun j => if h : j.val < n then s ⟨j.val,h⟩ else spare j

theorem first_spec {n : ℕ} (hn : n ≤ 19) (P : Program n) (before after : Fin n → List Bool)
    (spare : Fin 19 → List Bool) (ticks : ℕ) (h : RunSpec P before after ticks) :
    RunSpec (KS.W29.FixedSequential.liftPorts P (firstPorts n hn))
      (extend before spare) (extend after spare) ticks := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec P (firstPorts n hn) _ _ _ _ _ h
  · intro i
    change dite (i.val < n) (fun h => before ⟨i.val, h⟩) _ = before i
    exact dite_eq_left i.isLt
  · intro i
    change dite (i.val < n) (fun h => after ⟨i.val, h⟩) _ = after i
    exact dite_eq_left i.isLt
  · intro j hj
    by_cases hb : j.val < n
    · exact (hj ⟨j.val,hb⟩ (Fin.ext rfl)).elim
    · simp [extend,hb]

def registers (input num den sign tape savedR savedQ temp : List Bool) : Fin 19 → List Bool :=
  ![input,[],[],[],[],[],[],[],[],[],num,den,sign,tape,[],[],savedR,savedQ,temp]

def inputState (wire : List Bool) := registers wire [] [] [] [] [] [] []
def outputState (wire : List Bool) := registers [] wire [] [] [] [] [] []

def parseProgram : Program 19 := KS.W29.FixedSequential.liftPorts
  KS.W06.SingleRationalParser.program (firstPorts 13 (by decide))
def serializeProgram : Program 19 := KS.W29.FixedSequential.liftPorts
  KS.W01.SignedRationalSerializer.program (firstPorts 13 (by decide))
def negateProgram : Program 19 := KS.W29.FixedSequential.liftPorts
  KS.W16.RationalSignAction.program (firstPorts 14 (by decide))
def addProgram : Program 19 := KS.W29.FixedSequential.liftPorts
  KS.W13.RationalAdd.program (firstPorts 16 (by decide))

def parsed (q r : ℚ) := registers (KS.W01.encodeRat r)
  (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den) [decide (q.num < 0)] [] [] [] []
def saved (q r : ℚ) := registers []
  (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den) [decide (q.num < 0)] [] (KS.W01.encodeRat r) [] []
def emitted (q r : ℚ) := registers [] (KS.W01.encodeRat q) [] [] [] (KS.W01.encodeRat r) [] []
def paired (q r : ℚ) := registers [] [] [] [] [] (KS.W01.encodeRat r) (KS.W01.encodeRat q) []
def prepared (q r : ℚ) := registers (KS.W01.encodeRat r) [] [] [] [] [] (KS.W01.encodeRat q) []
def marked (q r : ℚ) := registers (KS.W01.encodeRat r) [] [] [] [false] [] (KS.W01.encodeRat q) []
def negated (q r : ℚ) := registers [] (KS.W01.encodeRat (-r)) [] [] [false] [] (KS.W01.encodeRat q) []
def cleared (q r : ℚ) := registers [] (KS.W01.encodeRat (-r)) [] [] [] [] (KS.W01.encodeRat q) []
def withRight (q r : ℚ) := registers (KS.W01.encodeRat (-r)) [] [] [] [] [] (KS.W01.encodeRat q) []

theorem parse_spec (q r : ℚ) :
    RunSpec parseProgram (inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat r)) (parsed q r)
      (8 * (KS.W01.ratLength q + 1)) := by
  have h := first_spec (by decide : 13 ≤ 19) KS.W06.SingleRationalParser.program _ _ (fun _ => []) _
    (KS.W06.SingleRationalParser.canonical_spec q (KS.W01.encodeRat r))
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)

theorem saveR_spec (q r : ℚ) :
    RunSpec (KS.W12.FixedDot.transferProgram 0 16) (parsed q r) (saved q r)
      (2 * KS.W01.ratLength r + 2) := by
  have h := KS.W12.FixedDot.transfer_spec 0 16 (by decide) (by decide) (by decide) (parsed q r) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> simp [KS.W12.FixedDot.transferAfter,parsed,saved,registers])

def serializeTicks (q : ℚ) := 16 * ((Computability.encodeNat q.num.natAbs).length +
  (Computability.encodeNat q.den).length + 1)

theorem serialize_spec (q r : ℚ) :
    RunSpec serializeProgram (saved q r) (emitted q r) (serializeTicks q) := by
  have h := first_spec (by decide : 13 ≤ 19) KS.W01.SignedRationalSerializer.program _ _
    (fun j => if j=16 then KS.W01.encodeRat r else []) _
    (KS.W01.SignedRationalSerializer.serializes_rational q)
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)

theorem saveQ_spec (q r : ℚ) :
    RunSpec (KS.W12.FixedDot.transferProgram 10 17) (emitted q r) (paired q r)
      (2 * KS.W01.ratLength q + 2) := by
  have h := KS.W12.FixedDot.transfer_spec 10 17 (by decide) (by decide) (by decide) (emitted q r) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> simp [KS.W12.FixedDot.transferAfter,emitted,paired,registers])

theorem takeR_spec (q r : ℚ) :
    RunSpec (KS.W12.FixedDot.transferProgram 16 0) (paired q r) (prepared q r)
      (2 * KS.W01.ratLength r + 2) := by
  have h := KS.W12.FixedDot.transfer_spec 16 0 (by decide) (by decide) (by decide) (paired q r) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> simp [KS.W12.FixedDot.transferAfter,paired,prepared,registers])

def markDispatch (_ : Fin 1) (_ : Fin 19 → Fin 3) (_ : Bool) : Instruction 19 1 :=
  ⟨none,Vector.ofFn (fun j => if j=13 then .push false else .stay)⟩
def markProgram : Program 19 := ofMachine (compile 0 0 13 markDispatch)

theorem mark_spec (q r : ℚ) : RunSpec markProgram (prepared q r) (marked q r) 1 := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine (compile (0 : Fin 1) (0 : Fin 19) 13 markDispatch)
  intro bits hb
  cases bits with
  | nil => simp at hb
  | cons coin tail =>
    have ht : tail = [] := List.length_eq_zero_iff.mp (by simpa using hb)
    subst tail
    change (compile (0 : Fin 1) (0 : Fin 19) 13 markDispatch).step
      ⟨some (0 : Fin 1), prepared q r⟩ coin = _
    erw [step_compile]
    apply congrArg₂ Config.mk
    · rfl
    · funext j
      fin_cases j <;> rfl

theorem negate_spec (q r : ℚ) :
    RunSpec negateProgram (marked q r) (negated q r) (64 * (KS.W01.ratLength r + 1)) := by
  have h := first_spec (by decide : 14 ≤ 19) KS.W16.RationalSignAction.program _ _
    (fun j => if j=17 then KS.W01.encodeRat q else []) _
    (KS.W16.RationalSignAction.negation_spec r [])
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)

theorem clearMark_spec (q r : ℚ) :
    RunSpec (KS.W04.BinaryStackMoves.clearProgram 13) (negated q r) (cleared q r) 2 := by
  have h := KS.W15.RationalMultiply.clear_spec (13 : Fin 19) (negated q r)
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)

theorem placeRight_spec (q r : ℚ) :
    RunSpec (KS.W12.FixedDot.transferProgram 10 0) (cleared q r) (withRight q r)
      (2 * KS.W01.ratLength (-r) + 2) := by
  have h := KS.W12.FixedDot.transfer_spec 10 0 (by decide) (by decide) (by decide) (cleared q r) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> simp [KS.W12.FixedDot.transferAfter,cleared,withRight,registers])

theorem prependLeft_spec (q r : ℚ) :
    RunSpec (KS.W12.FixedDot.transferProgram 17 0) (withRight q r)
      (inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat (-r))) (2 * KS.W01.ratLength q + 2) := by
  have h := KS.W12.FixedDot.transfer_spec 17 0 (by decide) (by decide) (by decide) (withRight q r) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> simp [KS.W12.FixedDot.transferAfter,withRight,inputState,registers])

theorem addition_spec (q r : ℚ) :
    RunSpec addProgram (inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat (-r)))
      (outputState (KS.W01.encodeRat (q-r)))
      (KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat (-r)).length) := by
  have h := first_spec (by decide : 16 ≤ 19) KS.W13.RationalAdd.program _ _ (fun _ => []) _
    (KS.W13.RationalAdd.polynomial_spec q (-r))
  rw [← sub_eq_add_neg] at h
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)

def prepareProgram : Program 19 := compose (compose (compose (compose
  parseProgram (KS.W12.FixedDot.transferProgram 0 16)) serializeProgram)
  (KS.W12.FixedDot.transferProgram 10 17)) (KS.W12.FixedDot.transferProgram 16 0)
def changeSignProgram : Program 19 := compose (compose (compose (compose markProgram negateProgram)
  (KS.W04.BinaryStackMoves.clearProgram 13)) (KS.W12.FixedDot.transferProgram 10 0))
  (KS.W12.FixedDot.transferProgram 17 0)
def program : Program 19 := compose (compose prepareProgram changeSignProgram) addProgram
def machine : Machine := program.toMachine

def prepareTicks (q r : ℚ) := (((8*(KS.W01.ratLength q+1)+(2*KS.W01.ratLength r+2))+
  serializeTicks q)+(2*KS.W01.ratLength q+2))+(2*KS.W01.ratLength r+2)
def changeSignTicks (q r : ℚ) := (((1+64*(KS.W01.ratLength r+1))+2)+
  (2*KS.W01.ratLength (-r)+2))+(2*KS.W01.ratLength q+2)
def totalTicks (q r : ℚ) := prepareTicks q r + changeSignTicks q r +
  KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat (-r)).length

theorem full_spec (q r : ℚ) :
    RunSpec program (inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat r))
      (outputState (KS.W01.encodeRat (q-r))) (totalTicks q r) := by
  have hp := (((parse_spec q r).compose (saveR_spec q r)).compose (serialize_spec q r)).compose (saveQ_spec q r)
  have hp' := hp.compose (takeR_spec q r)
  have hn := (((mark_spec q r).compose (negate_spec q r)).compose (clearMark_spec q r)).compose (placeRight_spec q r)
  have hn' := hn.compose (prependLeft_spec q r)
  exact (hp'.compose hn').compose (addition_spec q r)

end KS.W13.RationalSubtract

end OAI
