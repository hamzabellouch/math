import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.DivisionInput
import OAI.Analysis.MatrixSigning.Arithmetic.DivisionOutput

namespace OAI

namespace KS.W19.EncodedDivision
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def program : Program 10 := compose DivisionInput.program DivisionOutput.program
def machine : Machine := program.toMachine

def resultPair (xs d : List Bool) : List Bool × List Bool := DivisionLoop.process d xs.reverse [] []

theorem input_spec (xs d : List Bool) :
    RunSpec DivisionInput.program
      (DivisionInput.machine.init (KS.W01.frame xs ++ KS.W01.frame d)).«stacks»
      (DivisionMachine.«stacks» d [] (resultPair xs d).1 (resultPair xs d).2 [] [] [] [])
      (DivisionInput.inputFuel xs d) := by
  intro bits hb
  exact DivisionInput.run_input_tape xs d bits hb

theorem run_spec (xs d : List Bool) :
    RunSpec program (DivisionInput.machine.init (KS.W01.frame xs ++ KS.W01.frame d)).«stacks»
      (DivisionMachine.«stacks» d [] [] (DivisionOutput.pairWire (resultPair xs d).1 (resultPair xs d).2)
        [] [] [] [])
      (DivisionInput.inputFuel xs d + 6 * (resultPair xs d).1.length + 6 * (resultPair xs d).2.length + 9) := by
  have h := (input_spec xs d).compose
    (DivisionOutput.output_spec d (resultPair xs d).1 (resultPair xs d).2)
  apply h.mono
  omega

theorem fuel_quadratic (xs d : List Bool) :
    DivisionInput.inputFuel xs d + 6 * (resultPair xs d).1.length + 6 * (resultPair xs d).2.length + 9 ≤
      KS.W29.polynomialFuel 32 2 (KS.W01.frame xs ++ KS.W01.frame d).length := by
  have hq := DivisionLoop.process_quotient_length d xs.reverse [] []
  have hr := DivisionLoop.process_remainder_length d xs.reverse [] []
  simp only [List.length_nil, List.length_reverse, Nat.zero_add, Nat.zero_max] at hq hr
  change (resultPair xs d).1.length = xs.length at hq
  change (resultPair xs d).2.length ≤ d.length + xs.length at hr
  rw [hq]
  simp only [DivisionInput.inputFuel, KS.W29.polynomialFuel, List.length_append, KS.W01.length_frame]
  nlinarith [Nat.zero_le (xs.length * d.length), Nat.zero_le (xs.length ^ 2), Nat.zero_le (d.length ^ 2)]

theorem run_polynomial (xs d bits : List Bool)
    (hb : bits.length = KS.W29.polynomialFuel 32 2 (KS.W01.frame xs ++ KS.W01.frame d).length) :
    machine.run (machine.init (KS.W01.frame xs ++ KS.W01.frame d)) bits =
      ⟨none, DivisionMachine.«stacks» d [] []
        (DivisionOutput.pairWire (resultPair xs d).1 (resultPair xs d).2) [] [] [] []⟩ := by
  exact (run_spec xs d).run_of_le bits (by rw [hb]; exact fuel_quadratic xs d)

theorem output_polynomial (xs d bits : List Bool)
    (hb : bits.length = KS.W29.polynomialFuel 32 2 (KS.W01.frame xs ++ KS.W01.frame d).length) :
    machine.output (KS.W01.frame xs ++ KS.W01.frame d) bits =
      KS.W01.encodeNat (bitsValue (resultPair xs d).1) ++ KS.W01.encodeNat (bitsValue (resultPair xs d).2) := by
  unfold Machine.output
  rw [run_polynomial xs d bits hb]
  rfl

theorem natural_output_correct (n d : Nat) (hd : 0 < d) (bits : List Bool)
    (hb : bits.length = KS.W29.polynomialFuel 32 2 (KS.W01.encodeNat n ++ KS.W01.encodeNat d).length) :
    ∃ q r : Nat,
      machine.output (KS.W01.encodeNat n ++ KS.W01.encodeNat d) bits = KS.W01.encodeNat q ++ KS.W01.encodeNat r ∧
      n = d*q+r ∧ r < d := by
  let qr := resultPair (Computability.encodeNat n) (Computability.encodeNat d)
  refine ⟨bitsValue qr.1, bitsValue qr.2, ?_, ?_⟩
  · exact output_polynomial (Computability.encodeNat n) (Computability.encodeNat d) bits hb
  · have h := DivisionLoop.process_payload_correct (Computability.encodeNat d) (Computability.encodeNat n)
      (by simpa only [bitsValue_encodeNat] using hd)
    simp only [bitsValue_encodeNat] at h
    exact h

theorem haltsWithin_polynomial (n d : Nat) :
    machine.HaltsWithin (KS.W01.encodeNat n ++ KS.W01.encodeNat d)
      (KS.W29.polynomialFuel 32 2 (KS.W01.encodeNat n ++ KS.W01.encodeNat d).length) := by
  intro seed
  change (machine.run (machine.init _) (List.ofFn seed)).state = none
  exact congrArg (fun c => c.state)
    (run_polynomial (Computability.encodeNat n) (Computability.encodeNat d)
      (List.ofFn seed) List.length_ofFn)

end KS.W19.EncodedDivision

end OAI
