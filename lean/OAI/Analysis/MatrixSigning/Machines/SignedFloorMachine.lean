import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedPortRunSpec
import OAI.Analysis.MatrixSigning.Machines.MachineRoundTrip
import OAI.Analysis.MatrixSigning.Machines.SignedFloorModel
import OAI.Analysis.MatrixSigning.Encoding.SignedQuotientSerializer
import OAI.Analysis.MatrixSigning.Arithmetic.EncodedDivision

namespace OAI

namespace KS.W19.SignedFloorMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def naturalPorts : Fin 10 ↪ Fin 11 :=
  Fin.castLEEmb (by decide)
def canonPorts : Fin 3 ↪ Fin 11 := ⟨![0,5,8], by decide⟩
def outputPorts : Fin 3 ↪ Fin 11 := ⟨![0,5,10], by decide⟩

def stripDispatch (_state : Fin 1) (heads : Fin 11 → Fin 3) (_coin : Bool) : Instruction 11 1 :=
  if (heads 0).val = 0 then Instruction.halt 11 1
  else ⟨none, Vector.ofFn (fun j => if j = 0 then .pop
    else if j = 10 then .push ((heads 0).val == 2) else .stay)⟩

def strip : Program 11 := ofMachine (compile 0 0 0 stripDispatch)
def divide : Program 11 := KS.W29.FixedSequential.liftPorts DivisionInput.program naturalPorts
def canon : Program 11 := FixedCanonicalize.program canonPorts
def emit : Program 11 := SignedQuotientSerializer.program outputPorts
def finish : Program 11 := compose canon emit
def tailProgram : Program 11 := compose divide finish
def program : Program 11 := compose strip tailProgram
def machine : Machine := program.toMachine

def «stacks» (input d q r sign : List Bool) : Fin 11 → List Bool :=
  ![input,[],d,[],r,q,[],[],[],[],sign]

theorem strip_spec (sign : Bool) (tail : List Bool) :
    RunSpec strip («stacks» (sign :: tail) [] [] [] []) («stacks» tail [] [] [] [sign]) 1 := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hb
  cases bits with
  | nil => simp at hb
  | cons coin rest =>
    have hr : rest = [] := by apply List.length_eq_zero_iff.mp; simpa using hb
    subst rest
    simp only [Machine.run]
    erw [step_compile]
    cases sign <;> apply KS.W19.FixedRun.config_ext
    all_goals first | rfl | (intro j; fin_cases j <;> rfl)

theorem divide_spec (sign : Bool) (xs d : List Bool) :
    RunSpec divide («stacks» (KS.W01.frame xs ++ KS.W01.frame d) [] [] [] [sign])
      («stacks» [] d (EncodedDivision.resultPair xs d).1 (EncodedDivision.resultPair xs d).2 [sign])
      (DivisionInput.inputFuel xs d) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec DivisionInput.program naturalPorts _ _ _ _ _
    (EncodedDivision.input_spec xs d)
  · intro i
    fin_cases i <;> rfl
  · intro i
    fin_cases i <;> rfl
  · intro j hj
    have hge : 10 ≤ j.val := by
      by_contra hn
      have hlt : j.val < 10 := by omega
      exact hj ⟨j.val, hlt⟩ (Fin.ext rfl)
    have he : j = 10 := Fin.ext (by have hh := j.isLt; omega)
    subst j
    rfl

theorem canon_spec (sign : Bool) (d q r : List Bool) :
    RunSpec canon («stacks» [] d q r [sign])
      («stacks» [] d (DivisionOutput.canonical q) r [sign]) (2 * q.length + 2) := by
  have h := FixedCanonicalize.canonicalize_spec canonPorts («stacks» [] d q r [sign]) [] q
  have hi : UnsignedPairSerializer.registers canonPorts («stacks» [] d q r [sign]) [] q [] =
      «stacks» [] d q r [sign] := by funext j; fin_cases j <;> rfl
  have ho : UnsignedPairSerializer.registers canonPorts («stacks» [] d q r [sign]) [] (DivisionOutput.canonical q) [] =
      «stacks» [] d (DivisionOutput.canonical q) r [sign] := by funext j; fin_cases j <;> rfl
  dsimp only [DivisionOutput.canonical] at ho
  simp only [hi, ho] at h
  exact h

theorem emit_spec (sign : Bool) (d q r : List Bool) :
    RunSpec emit («stacks» [] d q r [sign])
      («stacks» [] d (SignedQuotientSerializer.wire sign q) r []) (4 * q.length + 4) := by
  have h := SignedQuotientSerializer.serialize_spec outputPorts («stacks» [] d q r [sign]) sign q
  have hi : UnsignedPairSerializer.registers outputPorts («stacks» [] d q r [sign]) [] q [sign] =
      «stacks» [] d q r [sign] := by funext j; fin_cases j <;> rfl
  have ho : UnsignedPairSerializer.registers outputPorts («stacks» [] d q r [sign]) []
      (SignedQuotientSerializer.wire sign q) [] = «stacks» [] d (SignedQuotientSerializer.wire sign q) r [] := by
    funext j
    fin_cases j <;> rfl
  simp only [hi, ho] at h
  exact h

theorem finish_spec (sign : Bool) (d q r : List Bool) :
    RunSpec finish («stacks» [] d q r [sign])
      («stacks» [] d (sign :: KS.W01.encodeNat (bitsValue q)) r []) (6 * q.length + 6) := by
  have h := (canon_spec sign d q r).compose (emit_spec sign d (DivisionOutput.canonical q) r)
  apply h.mono
  have hl := DivisionOutput.canonical_length q
  omega

theorem program_spec (sign : Bool) (xs d : List Bool) :
    RunSpec program («stacks» (sign :: (KS.W01.frame xs ++ KS.W01.frame d)) [] [] [] [])
      («stacks» [] d (sign :: KS.W01.encodeNat (bitsValue (EncodedDivision.resultPair xs d).1))
        (EncodedDivision.resultPair xs d).2 [])
      (1 + (DivisionInput.inputFuel xs d + (6 * (EncodedDivision.resultPair xs d).1.length + 6))) :=
  (strip_spec sign (KS.W01.frame xs ++ KS.W01.frame d)).compose
    ((divide_spec sign xs d).compose
      (finish_spec sign d (EncodedDivision.resultPair xs d).1 (EncodedDivision.resultPair xs d).2))

theorem fuel_quadratic (sign : Bool) (xs d : List Bool) :
    1 + (DivisionInput.inputFuel xs d + (6 * (EncodedDivision.resultPair xs d).1.length + 6)) ≤
      KS.W29.polynomialFuel 32 2 (sign :: (KS.W01.frame xs ++ KS.W01.frame d)).length := by
  have hq := DivisionLoop.process_quotient_length d xs.reverse [] []
  simp only [List.length_nil, List.length_reverse, Nat.zero_add] at hq
  change (EncodedDivision.resultPair xs d).1.length = xs.length at hq
  rw [hq]
  simp only [DivisionInput.inputFuel, KS.W29.polynomialFuel, List.length_cons, List.length_append, KS.W01.length_frame]
  nlinarith [Nat.zero_le (xs.length * d.length), Nat.zero_le (xs.length ^ 2), Nat.zero_le (d.length ^ 2)]

theorem run_signed_payload (sign : Bool) (xs d bits : List Bool)
    (hb : bits.length = KS.W29.polynomialFuel 32 2 (sign :: (KS.W01.frame xs ++ KS.W01.frame d)).length) :
    machine.run (machine.init (sign :: (KS.W01.frame xs ++ KS.W01.frame d))) bits =
      ⟨none, «stacks» [] d (sign :: KS.W01.encodeNat (bitsValue (EncodedDivision.resultPair xs d).1))
        (EncodedDivision.resultPair xs d).2 []⟩ := by
  have h := (program_spec sign xs d).run_of_le bits (by rw [hb]; exact fuel_quadratic sign xs d)
  have hi : machine.init (sign :: (KS.W01.frame xs ++ KS.W01.frame d)) =
      (⟨some program.initial, «stacks» (sign :: (KS.W01.frame xs ++ KS.W01.frame d)) [] [] [] []⟩ : Config 11 program.states) := by
    apply KS.W19.FixedRun.config_ext
    · rfl
    · intro j
      fin_cases j <;> rfl
  rw [hi]
  exact h

theorem output_floor (q : Rat) (bits : List Bool)
    (hb : bits.length = KS.W29.polynomialFuel 32 2 (KS.W01.encodeRat q).length) :
    machine.output (KS.W01.encodeRat q) bits = KS.W01.encodeInt ⌊q⌋ := by
  rw [SignedFloor.encodeRat_constructor] at hb ⊢
  simp only [KS.W01.encodeNat] at hb ⊢
  unfold Machine.output
  rw [run_signed_payload (negativeOfInt q.num) (Computability.encodeNat (KS.W01.intPayload q.num))
    (Computability.encodeNat q.den) bits hb]
  exact SignedFloor.floor_wire q

theorem haltsWithin_polynomial (q : Rat) :
    machine.HaltsWithin (KS.W01.encodeRat q) (KS.W29.polynomialFuel 32 2 (KS.W01.encodeRat q).length) := by
  intro seed
  change (machine.run (machine.init _) (List.ofFn seed)).state = none
  have hbits : (List.ofFn seed).length =
      KS.W29.polynomialFuel 32 2 (KS.W01.encodeRat q).length := List.length_ofFn
  have hin : KS.W01.encodeRat q = negativeOfInt q.num ::
      (KS.W01.frame (Computability.encodeNat (KS.W01.intPayload q.num)) ++
        KS.W01.frame (Computability.encodeNat q.den)) := by
    simp only [SignedFloor.encodeRat_constructor,KS.W01.encodeNat]
  have h := run_signed_payload (negativeOfInt q.num)
    (Computability.encodeNat (KS.W01.intPayload q.num)) (Computability.encodeNat q.den)
    (List.ofFn seed) (hbits.trans
      (congrArg (fun input : List Bool => KS.W29.polynomialFuel 32 2 input.length) hin))
  exact (congrArg (fun input : List Bool =>
    (machine.run (machine.init input) (List.ofFn seed)).state) hin).trans
      (congrArg Config.state h)

end KS.W19.SignedFloorMachine

end OAI
