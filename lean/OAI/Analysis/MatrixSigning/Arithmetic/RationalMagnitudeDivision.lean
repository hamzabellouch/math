import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedCanonicalize
import OAI.Analysis.MatrixSigning.Arithmetic.RationalMagnitudeSetup

namespace OAI

section

namespace KS.W30.RationalMagnitudeMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

def divisionWork (g x : List Bool) : Fin 10 → List Bool :=
  DivisionMachine.«stacks» g x.reverse [] [] [] [] [] []
def quotientWork (g q r : List Bool) : Fin 10 → List Bool :=
  DivisionMachine.«stacks» g [] q r [] [] [] []
def reversedQuotientWork (g q r : List Bool) : Fin 10 → List Bool :=
  DivisionMachine.«stacks» g [] [] r [] [] q.reverse []
def remainderWork (g r : List Bool) : Fin 10 → List Bool :=
  DivisionMachine.«stacks» g [] [] r [] [] [] []

theorem divide_spec (g x n d : List Bool) (s : Bool) (L : ℕ)
    (hg : g.length ≤ L) (hx : x.length ≤ L) :
    let qr := DivisionLoop.process g x.reverse [] []
    RunSpec divide («stacks» (divisionWork g x) n d s)
      («stacks» (quotientWork g qr.1 qr.2) n d s) (40 * (L + 1) ^ 2) := by
  dsimp only
  have h : RunSpec DivisionMachine.loop (divisionWork g x)
      (quotientWork g (DivisionLoop.process g x.reverse [] []).1
        (DivisionLoop.process g x.reverse [] []).2)
      (x.length * (8 * (x.length + 2 * g.length + 2) + 1) + 1) := by
    intro bits hlen
    exact DivisionMachine.loop_payload g x bits (by omega)
  have hm : x.length * (8 * (x.length + 2 * g.length + 2) + 1) ≤
      L * (8 * (3 * L + 2) + 1) := Nat.mul_le_mul hx (by omega)
  have ht : x.length * (8 * (x.length + 2 * g.length + 2) + 1) + 1 ≤
      40 * (L + 1) ^ 2 := by nlinarith
  exact core_spec DivisionMachine.loop _ _ n d s _ (h.mono ht)

theorem reverseQuotient_spec (g q r n d : List Bool) (s : Bool) :
    RunSpec reverseQuotient («stacks» (quotientWork g q r) n d s)
      («stacks» (reversedQuotientWork g q r) n d s) (q.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_move_stacks (5 : Fin 13) 8 (by decide)
    («stacks» (quotientWork g q r) n d s) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (5 : Fin 13) 8) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [«stacks»,quotientWork,reversedQuotientWork,
      DivisionMachine.«stacks»,KS.W04.BinaryStackMoves.twoConfig]

theorem clearRemainder_spec (g r n d : List Bool) (s : Bool) :
    RunSpec clearRemainder («stacks» (remainderWork g r) n d s)
      (divisorState g n d s) (r.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_clear_stacks (4 : Fin 13)
    («stacks» (remainderWork g r) n d s) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.clearMachine (4 : Fin 13)) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem takeNumerator_spec (g n d : List Bool) (sgn : Bool) :
    RunSpec takeNumerator (divisorState g n d sgn)
      («stacks» (divisionWork g n) [] d sgn) (n.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_move_stacks (10 : Fin 13) 3 (by decide)
    (divisorState g n d sgn) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (10 : Fin 13) 3) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [«stacks»,divisorState,divisorWork,
      divisionWork,DivisionMachine.«stacks»,KS.W04.BinaryStackMoves.twoConfig]

private theorem trimNumerator_input (g q r _numerator d : List Bool) (sgn : Bool) :
    UnsignedPairSerializer.registers numeratorTrimPorts («stacks» (remainderWork g r) [] d sgn) [] [] q.reverse=
      «stacks» (reversedQuotientWork g q r) [] d sgn :=by
  funext j
  fin_cases j <;> simp [UnsignedPairSerializer.registers,numeratorTrimPorts,«stacks»,
    remainderWork,reversedQuotientWork,DivisionMachine.«stacks»]

private theorem trimNumerator_output (g q r _numerator d : List Bool) (sgn : Bool) :
    UnsignedPairSerializer.registers numeratorTrimPorts («stacks» (remainderWork g r) [] d sgn)
      [] (trimBits q) []=«stacks» (remainderWork g r) (trimBits q) d sgn :=by
  funext j
  fin_cases j <;> simp [UnsignedPairSerializer.registers,numeratorTrimPorts,«stacks»,
    remainderWork,DivisionMachine.«stacks»]

theorem trimNumerator_spec (g q r n d : List Bool) (sgn : Bool) :
    RunSpec trimNumerator («stacks» (reversedQuotientWork g q r) [] d sgn)
      («stacks» (remainderWork g r) (trimBits q) d sgn) (q.length+1) :=by
  have h :=FixedCanonicalize.trim_spec numeratorTrimPorts («stacks» (remainderWork g r) [] d sgn) [] q
  rw [←trimBits_eq_encodeNat,trimNumerator_input g q r n d sgn,
    trimNumerator_output g q r n d sgn] at h
  exact h

theorem reduceNumerator_spec (g n d : List Bool) (sgn : Bool) (L : ℕ)
    (hg : g.length ≤ L) (hx : n.length ≤ L) :
    let qr := DivisionLoop.process g n.reverse [] []
    RunSpec reduceNumerator (divisorState g n d sgn)
      (divisorState g (trimBits qr.1) (d) sgn) (50 * (L + 1) ^ 2) := by
  dsimp only
  let qr := DivisionLoop.process g n.reverse [] []
  have h := (takeNumerator_spec g n d sgn).compose
    ((divide_spec g n [] d sgn L hg hx).compose
      ((reverseQuotient_spec g qr.1 qr.2 [] d sgn).compose
        ((trimNumerator_spec g qr.1 qr.2 n d sgn).compose
          (clearRemainder_spec g qr.2 (trimBits qr.1) (d) sgn))))
  have hq : qr.1.length = n.length := by
    simpa only [qr, List.length_reverse, List.length_nil, Nat.add_zero] using
      GCDMachine.process_quotient_length g n.reverse [] []
  have hr : qr.2.length ≤ 2 * L := by
    have hh := GCDMachine.process_remainder_length g n.reverse [] [] (2 * L)
      (by simp only [List.length_nil, List.length_reverse]; omega)
      (by simp only [List.length_reverse]; omega)
    exact hh
  have ht : (n.length + 1) + (40 * (L + 1) ^ 2 +
      ((qr.1.length + 1) + ((qr.1.length + 1) + (qr.2.length + 1)))) ≤
      50 * (L + 1) ^ 2 := by rw [hq]; nlinarith
  exact h.mono ht

theorem takeDenominator_spec (g n d : List Bool) (sgn : Bool) :
    RunSpec takeDenominator (divisorState g n d sgn)
      («stacks» (divisionWork g d) n [] sgn) (d.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_move_stacks (11 : Fin 13) 3 (by decide)
    (divisorState g n d sgn) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (11 : Fin 13) 3) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [«stacks»,divisorState,divisorWork,
      divisionWork,DivisionMachine.«stacks»,KS.W04.BinaryStackMoves.twoConfig]

private theorem trimDenominator_input (g q r n _denominator : List Bool) (sgn : Bool) :
    UnsignedPairSerializer.registers denominatorTrimPorts («stacks» (remainderWork g r) n [] sgn) [] [] q.reverse=
      «stacks» (reversedQuotientWork g q r) n [] sgn :=by
  funext j
  fin_cases j <;> simp [UnsignedPairSerializer.registers,denominatorTrimPorts,«stacks»,
    remainderWork,reversedQuotientWork,DivisionMachine.«stacks»]

private theorem trimDenominator_output (g q r n _denominator : List Bool) (sgn : Bool) :
    UnsignedPairSerializer.registers denominatorTrimPorts («stacks» (remainderWork g r) n [] sgn)
      [] (trimBits q) []=«stacks» (remainderWork g r) n (trimBits q) sgn :=by
  funext j
  fin_cases j <;> simp [UnsignedPairSerializer.registers,denominatorTrimPorts,«stacks»,
    remainderWork,DivisionMachine.«stacks»]

theorem trimDenominator_spec (g q r n d : List Bool) (sgn : Bool) :
    RunSpec trimDenominator («stacks» (reversedQuotientWork g q r) n [] sgn)
      («stacks» (remainderWork g r) n (trimBits q) sgn) (q.length+1) :=by
  have h :=FixedCanonicalize.trim_spec denominatorTrimPorts («stacks» (remainderWork g r) n [] sgn) [] q
  rw [←trimBits_eq_encodeNat,trimDenominator_input g q r n d sgn,
    trimDenominator_output g q r n d sgn] at h
  exact h

theorem reduceDenominator_spec (g n d : List Bool) (sgn : Bool) (L : ℕ)
    (hg : g.length ≤ L) (hx : d.length ≤ L) :
    let qr := DivisionLoop.process g d.reverse [] []
    RunSpec reduceDenominator (divisorState g n d sgn)
      (divisorState g (n) (trimBits qr.1) sgn) (50 * (L + 1) ^ 2) := by
  dsimp only
  let qr := DivisionLoop.process g d.reverse [] []
  have h := (takeDenominator_spec g n d sgn).compose
    ((divide_spec g d n [] sgn L hg hx).compose
      ((reverseQuotient_spec g qr.1 qr.2 n [] sgn).compose
        ((trimDenominator_spec g qr.1 qr.2 n d sgn).compose
          (clearRemainder_spec g qr.2 (n) (trimBits qr.1) sgn))))
  have hq : qr.1.length = d.length := by
    simpa only [qr, List.length_reverse, List.length_nil, Nat.add_zero] using
      GCDMachine.process_quotient_length g d.reverse [] []
  have hr : qr.2.length ≤ 2 * L := by
    have hh := GCDMachine.process_remainder_length g d.reverse [] [] (2 * L)
      (by simp only [List.length_nil, List.length_reverse]; omega)
      (by simp only [List.length_reverse]; omega)
    exact hh
  have ht : (d.length + 1) + (40 * (L + 1) ^ 2 +
      ((qr.1.length + 1) + ((qr.1.length + 1) + (qr.2.length + 1)))) ≤
      50 * (L + 1) ^ 2 := by rw [hq]; nlinarith
  exact h.mono ht

end KS.W30.RationalMagnitudeMachine

end

end OAI
