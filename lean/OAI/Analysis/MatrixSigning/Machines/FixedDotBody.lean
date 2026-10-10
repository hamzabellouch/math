import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalAddProgram
import OAI.Analysis.MatrixSigning.Machines.FixedDotPrimitives

namespace OAI

namespace KS.W12.FixedDot

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def additionProgram : Program 19 :=
  KS.W29.FixedSequential.liftPorts KS.W13.RationalAdd.program (initialPorts 16 (by decide))

theorem addition_spec (rem : List Bool) (a b : ℚ) :
    RunSpec additionProgram (registers rem (KS.W01.encodeRat a ++ KS.W01.encodeRat b) [] [] [])
      (registers rem [] (KS.W01.encodeRat (a + b)) [] [])
      (KS.W13.RationalAdd.totalTicks a b) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (KS.W13.RationalAdd.full_spec a b)
  · intro i
    fin_cases i <;> rfl
  · intro i
    fin_cases i <;> rfl
  · intro j hj
    have h0 : j ≠ 0 := hj 0
    have h10 : j ≠ 10 := hj 10
    simp [registers, h0, h10]

theorem transfer_product_spec (rem product acc : List Bool) :
    RunSpec (transferProgram 10 0) (registers rem [] product acc [])
      (registers rem product [] acc []) (2 * product.length + 2) := by
  have h := transfer_spec 10 0 (by decide) (by decide) (by decide)
    (registers rem [] product acc []) rfl
  convert h using 1 <;> (try rfl)
  funext j
  fin_cases j <;> simp [transferAfter, registers]

theorem transfer_accumulator_spec (rem product acc : List Bool) :
    RunSpec (transferProgram 17 0) (registers rem product [] acc [])
      (registers rem (acc ++ product) [] [] []) (2 * acc.length + 2) := by
  have h := transfer_spec 17 0 (by decide) (by decide) (by decide)
    (registers rem product [] acc []) rfl
  convert h using 1 <;> (try rfl)
  funext j
  fin_cases j <;> simp [transferAfter, registers]

theorem store_accumulator_spec (rem value : List Bool) :
    RunSpec (transferProgram 10 17) (registers rem [] value [] [])
      (registers rem [] [] value []) (2 * value.length + 2) := by
  have h := transfer_spec 10 17 (by decide) (by decide) (by decide)
    (registers rem [] value [] []) rfl
  convert h using 1 <;> (try rfl)
  funext j
  fin_cases j <;> simp [transferAfter, registers]

def body : Program 19 :=
  compose (compose (compose (compose (compose decodeProgram multiplyProgram)
    (transferProgram 10 0)) (transferProgram 17 0)) additionProgram) (transferProgram 10 17)

def bodyTicks (p : ℚ × ℚ) (a : ℚ) : ℕ :=
  (((((3 * (pairPayload p).length + 2) + KS.W15.RationalMultiply.totalTicks p.1 p.2) +
    (2 * (KS.W01.encodeRat (p.1 * p.2)).length + 2)) +
    (2 * (KS.W01.encodeRat a).length + 2)) +
    KS.W13.RationalAdd.totalTicks a (p.1 * p.2)) +
    (2 * (KS.W01.encodeRat (a + p.1 * p.2)).length + 2)

theorem body_spec (p : ℚ × ℚ) (ps : List (ℚ × ℚ)) (a : ℚ) :
    RunSpec body (boundary (inputWire (p :: ps)) a)
      (boundary (inputWire ps) (a + p.1 * p.2)) (bodyTicks p a) := by
  exact (((((decode_spec (pairPayload p) (inputWire ps) (KS.W01.encodeRat a)).compose
    (multiplication_spec (inputWire ps) (KS.W01.encodeRat a) p)).compose
    (transfer_product_spec (inputWire ps) (KS.W01.encodeRat (p.1 * p.2)) (KS.W01.encodeRat a))).compose
    (transfer_accumulator_spec (inputWire ps) (KS.W01.encodeRat (p.1 * p.2)) (KS.W01.encodeRat a))).compose
    (addition_spec (inputWire ps) a (p.1 * p.2))).compose
    (store_accumulator_spec (inputWire ps) (KS.W01.encodeRat (a + p.1 * p.2)))

theorem run_dot_loop (ps : List (ℚ × ℚ)) (a : ℚ) (bits : List Bool)
    (hlen : loopTicks bodyTicks ps a ≤ bits.length) :
    (loopProgram body).toMachine.run (loopConfig body (inputWire ps) a) bits =
      ⟨none, boundary [] (a + dotValue ps)⟩ :=
  run_loop_of_body_spec body bodyTicks body_spec ps a bits hlen

theorem dot_loop_spec (ps : List (ℚ × ℚ)) (a : ℚ) :
    RunSpec (loopProgram body) (boundary (inputWire ps) a)
      (boundary [] (a + dotValue ps)) (loopTicks bodyTicks ps a) := by
  intro bits hbits
  exact run_dot_loop ps a bits hbits.ge

end KS.W12.FixedDot

end OAI
