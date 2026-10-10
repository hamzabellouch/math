import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.WirePrimitives
import OAI.Analysis.MatrixSigning.Optimization.SignedFloorInterface
import OAI.Analysis.MatrixSigning.Machines.SignedFloorSize

namespace OAI

namespace KS.W20.FloorRationalMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19

abbrev Registers := Fin 11 → List Bool

def state (input output : List Bool) : Registers :=
  SignedFloorMachine.«stacks» input [] output [] []

def clearDivisor : Program 11 := KS.W04.BinaryStackMoves.clearProgram 2
def clearRemainder : Program 11 := KS.W04.BinaryStackMoves.clearProgram 4

def clearScratch : Program 11 := compose clearDivisor clearRemainder

theorem clearScratch_spec (d q r : List Bool) :
    RunSpec clearScratch (SignedFloorMachine.«stacks» [] d q r []) (state [] q)
      (d.length + r.length + 2) := by
  have h₁ : RunSpec clearDivisor (SignedFloorMachine.«stacks» [] d q r [])
      (SignedFloorMachine.«stacks» [] [] q r []) (d.length + 1) := by
    convert KS.W15.RationalMultiply.clear_spec (2 : Fin 11)
      (SignedFloorMachine.«stacks» [] d q r []) using 1 <;> (try rfl)
    funext j
    fin_cases j <;> rfl
  have h₂ : RunSpec clearRemainder (SignedFloorMachine.«stacks» [] [] q r [])
      (state [] q) (r.length + 1) := by
    convert KS.W15.RationalMultiply.clear_spec (4 : Fin 11)
      (SignedFloorMachine.«stacks» [] [] q r []) using 1 <;> (try rfl)
    funext j
    fin_cases j <;> rfl
  convert h₁.compose h₂ using 1 <;> (try rfl)
  omega

def appendDenominator : Program 11 :=
  compose (KS.W04.BinaryStackMoves.moveProgram (5 : Fin 11) 0)
    (compose (Wire.writeBits (5 : Fin 11) (KS.W01.encodeNat 1))
      (KS.W04.BinaryStackMoves.moveProgram (0 : Fin 11) 5))

theorem appendDenominator_spec (wire : List Bool) :
    RunSpec appendDenominator (state [] wire) (state [] (wire ++ KS.W01.encodeNat 1))
      (2 * wire.length + 6) := by
  have h₁ : RunSpec (KS.W04.BinaryStackMoves.moveProgram (5 : Fin 11) 0)
      (state [] wire) (state wire.reverse []) (wire.length + 1) := by
    convert KS.W15.RationalMultiply.move_spec (5 : Fin 11) 0 (by decide) (state [] wire) using 1 <;> (try rfl)
    funext j
    fin_cases j <;> simp [state, SignedFloorMachine.«stacks», KS.W15.RationalMultiply.moveAfter]
  have h₂ : RunSpec (Wire.writeBits (5 : Fin 11) (KS.W01.encodeNat 1))
      (state wire.reverse []) (state wire.reverse (KS.W01.encodeNat 1)) 4 := by
    convert Wire.writeBits_spec (5 : Fin 11) (KS.W01.encodeNat 1) (state wire.reverse []) using 1 <;> (try rfl)
    · funext j
      fin_cases j <;> simp [state, SignedFloorMachine.«stacks», Function.update]
  have h₃ : RunSpec (KS.W04.BinaryStackMoves.moveProgram (0 : Fin 11) 5)
      (state wire.reverse (KS.W01.encodeNat 1)) (state [] (wire ++ KS.W01.encodeNat 1))
      (wire.length + 1) := by
    convert KS.W15.RationalMultiply.move_spec (0 : Fin 11) 5 (by decide)
      (state wire.reverse (KS.W01.encodeNat 1)) using 1
    · funext j
      fin_cases j <;> simp [state, SignedFloorMachine.«stacks», KS.W15.RationalMultiply.moveAfter]
    · simp [state, SignedFloorMachine.«stacks»]
  convert h₁.compose (h₂.compose h₃) using 1 <;> (try rfl)
  omega

def program : Program 11 := compose SignedFloorMachine.program (compose clearScratch appendDenominator)
def machine : Machine := program.toMachine

def ticks (q : ℚ) : ℕ :=
  KS.W29.polynomialFuel 32 2 (KS.W01.encodeRat q).length +
    ((Computability.encodeNat q.den).length + (SignedFloorMachine.rationalRemainder q).length + 2 +
      (2 * (KS.W01.encodeInt ⌊q⌋).length + 6))

theorem encodeRat_intCast (z : ℤ) :
    KS.W01.encodeRat (z : ℚ) = KS.W01.encodeInt z ++ KS.W01.encodeNat 1 := by
  simp [KS.W01.encodeRat]

theorem full_spec (q : ℚ) :
    RunSpec program (state (KS.W01.encodeRat q) []) (state [] (KS.W01.encodeRat (⌊q⌋ : ℚ)))
      (ticks q) := by
  have h := (SignedFloorMachine.rational_runSpec q).compose
    ((clearScratch_spec (Computability.encodeNat q.den) (KS.W01.encodeInt ⌊q⌋)
      (SignedFloorMachine.rationalRemainder q)).compose
      (appendDenominator_spec (KS.W01.encodeInt ⌊q⌋)))
  simp only [encodeRat_intCast] at h ⊢
  exact h

theorem onPorts_spec {K : ℕ} (ports : Fin 11 ↪ Fin K)
    (before after : Fin K → List Bool) (q : ℚ)
    (hin : ∀ i, before (ports i) = state (KS.W01.encodeRat q) [] i)
    (hout : ∀ i, after (ports i) = state [] (KS.W01.encodeRat (⌊q⌋ : ℚ)) i)
    (hother : ∀ j, (∀ i, j ≠ ports i) → after j = before j) :
    RunSpec (KS.W29.FixedSequential.liftPorts program ports) before after (ticks q) :=
  KS.W01.FixedPortRunSpec.lift_runSpec program ports _ _ before after _
    (full_spec q) hin hout hother

theorem ticks_le_polynomial (q : ℚ) :
    ticks q ≤ KS.W29.polynomialFuel 64 2 (KS.W01.encodeRat q).length := by
  have hr := DivisionLoop.process_remainder_length (Computability.encodeNat q.den)
    (Computability.encodeNat (KS.W01.intPayload q.num)).reverse [] []
  simp only [List.length_nil, List.length_reverse, Nat.zero_max] at hr
  change (SignedFloorMachine.rationalRemainder q).length ≤
    (Computability.encodeNat q.den).length +
      (Computability.encodeNat (KS.W01.intPayload q.num)).length at hr
  have hi := SignedFloor.floor_encodeInt_length_le_input q
  have hparts : (Computability.encodeNat q.den).length +
      (Computability.encodeNat (KS.W01.intPayload q.num)).length ≤ (KS.W01.encodeRat q).length := by
    rw [KS.W01.length_encodeRat]
    change KS.W01.natPayloadLength q.den + KS.W01.natPayloadLength (KS.W01.intPayload q.num) ≤ _
    omega
  unfold ticks KS.W29.polynomialFuel
  nlinarith [Nat.zero_le ((KS.W01.encodeRat q).length ^ 2)]

theorem polynomial_spec (q : ℚ) :
    RunSpec program (state (KS.W01.encodeRat q) []) (state [] (KS.W01.encodeRat (⌊q⌋ : ℚ)))
      (KS.W29.polynomialFuel 64 2 (KS.W01.encodeRat q).length) :=
  (full_spec q).mono (ticks_le_polynomial q)

theorem init_eq (input : List Bool) : machine.init input =
    (⟨some program.initial, state input []⟩ : Config 11 program.states) := by
  apply KS.W19.FixedRun.config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem output_floor_rational (q : ℚ) (bits : List Bool)
    (hbits : KS.W29.polynomialFuel 64 2 (KS.W01.encodeRat q).length ≤ bits.length) :
    machine.output (KS.W01.encodeRat q) bits = KS.W01.encodeRat (⌊q⌋ : ℚ) := by
  unfold Machine.output
  rw [init_eq]
  change (program.toMachine.run ⟨some program.initial, state (KS.W01.encodeRat q) []⟩ bits).«stacks»
    (program.toMachine.outputStack) = _
  rw [(polynomial_spec q).run_of_le bits hbits]
  rfl

theorem halts_polynomial (q : ℚ) :
    machine.HaltsWithin (KS.W01.encodeRat q)
      (KS.W29.polynomialFuel 64 2 (KS.W01.encodeRat q).length) := by
  intro seed
  unfold Machine.runSeed
  rw [init_eq]
  change (program.toMachine.run ⟨some program.initial, state (KS.W01.encodeRat q) []⟩
    (List.ofFn seed)).state = none
  rw [(polynomial_spec q) (List.ofFn seed) (by simp only [List.length_ofFn])]

end KS.W20.FloorRationalMachine

end OAI
