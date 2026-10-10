import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedPortRunSpec
import OAI.Analysis.MatrixSigning.Complexity.GCDMachinePolynomial
import OAI.Analysis.MatrixSigning.Arithmetic.RationalMagnitudeMachine

namespace OAI

namespace KS.W30.RationalMagnitudeMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

theorem stacks_core (work : Fin 10 → List Bool) (num den : List Bool) (negative : Bool)
    (i : Fin 10) : «stacks» work num den negative (corePorts i)=work i :=by
  fin_cases i <;> rfl

theorem stacks_spare_value (work : Fin 10 → List Bool) (num den : List Bool)
    (negative : Bool) (j : Fin 13) (hj : 10≤j.val) :
    «stacks» work num den negative j=
      (if j=10 then num else if j=11 then den else [negative]) :=by
  have he : j.val=10 ∨ j.val=11 ∨ j.val=12 :=by omega
  rcases he with h | h | h
  · have he : j=10 :=Fin.ext h
    rw [he]
    simp [«stacks»]
  · have he : j=11 :=Fin.ext h
    rw [he]
    simp [«stacks»]
  · have he : j=12 :=Fin.ext h
    rw [he]
    simp [«stacks»]

theorem stacks_spare (before after : Fin 10 → List Bool) (num den : List Bool)
    (negative : Bool) (j : Fin 13) (hj : ∀i,j≠corePorts i) :
    «stacks» after num den negative j=«stacks» before num den negative j :=by
  have hn : 10≤j.val :=by
    by_contra hn
    have h : j.val<10 :=by omega
    exact hj ⟨j.val,h⟩ (Fin.ext rfl)
  rw [stacks_spare_value _ _ _ _ _ hn,stacks_spare_value _ _ _ _ _ hn]

theorem core_spec (P : Program 10) (before after : Fin 10 → List Bool)
    (num den : List Bool) (negative : Bool) (ticks : ℕ)
    (h : RunSpec P before after ticks) :
    RunSpec (KS.W29.FixedSequential.liftPorts P corePorts)
      («stacks» before num den negative) («stacks» after num den negative) ticks :=
  KS.W01.FixedPortRunSpec.lift_runSpec P corePorts before after
    («stacks» before num den negative) («stacks» after num den negative) ticks h
    (stacks_core before num den negative) (stacks_core after num den negative)
    (stacks_spare before after num den negative)

def copiedNumeratorWork (n : List Bool) : Fin 10 → List Bool :=
  ![[],n,[],[],[],[],[],[],[],[]]

theorem copyNumerator_spec (n d : List Bool) (s : Bool) :
    RunSpec copyNumerator (state n d s)
      («stacks» (copiedNumeratorWork n) n d s) (2 * n.length + 2) := by
  intro bits hlen
  have h := KS.W01.FixedCopy.run_copy_restore numeratorCopyPorts (state n d s)
    n bits rfl rfl rfl hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W01.FixedCopy.machine numeratorCopyPorts) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem reverseNumeratorCopy_spec (n d : List Bool) (s : Bool) :
    RunSpec reverseNumeratorCopy («stacks» (copiedNumeratorWork n) n d s)
      («stacks» (GCDMachine.state n []) n d s) (n.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_move_stacks (1 : Fin 13) 3 (by decide)
    («stacks» (copiedNumeratorWork n) n d s) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (1 : Fin 13) 3) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [«stacks»,copiedNumeratorWork,GCDMachine.state,DivisionMachine.«stacks»,KS.W04.BinaryStackMoves.twoConfig]

theorem copyDenominator_spec (n d : List Bool) (s : Bool) :
    RunSpec copyDenominator («stacks» (GCDMachine.state n []) n d s)
      («stacks» (GCDMachine.state n d) n d s) (2 * d.length + 2) := by
  intro bits hlen
  have h := KS.W01.FixedCopy.run_copy_restore denominatorCopyPorts
    («stacks» (GCDMachine.state n []) n d s) d bits rfl rfl rfl hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W01.FixedCopy.machine denominatorCopyPorts) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem prepare_spec (n d : List Bool) (s : Bool) :
    RunSpec prepare (state n d s) («stacks» (GCDMachine.state n d) n d s)
      (3 * n.length + 2 * d.length + 5) := by
  have h := (copyNumerator_spec n d s).compose
    ((reverseNumeratorCopy_spec n d s).compose (copyDenominator_spec n d s))
  convert h using 1 <;> first | rfl | omega

theorem gcd_spec (n d : List Bool) (s : Bool) (L : ℕ)
    (hnc : CanonicalBits n) (hdc : CanonicalBits d) (hn : n.length ≤ L) (hd : d.length ≤ L) :
    RunSpec gcd («stacks» (GCDMachine.state n d) n d s)
      («stacks» (GCDMachine.outputState
        (Computability.encodeNat (Nat.gcd (bitsValue n) (bitsValue d)))) n d s)
      (100 * (L + 1) ^ 3) :=
  core_spec GCDMachine.program _ _ n d s _ (GCDMachine.program_spec n d L hnc hdc hn hd)

def reversedGCDWork (g : List Bool) : Fin 10 → List Bool :=
  DivisionMachine.«stacks» [] [] [] [] [] [] g.reverse []
def divisorWork (g : List Bool) : Fin 10 → List Bool :=
  DivisionMachine.«stacks» g [] [] [] [] [] [] []
def divisorState (g n d : List Bool) (s : Bool) : Fin 13 → List Bool :=
  «stacks» (divisorWork g) n d s

theorem reverseGCD_spec (g n d : List Bool) (s : Bool) :
    RunSpec reverseGCD («stacks» (GCDMachine.outputState g) n d s)
      («stacks» (reversedGCDWork g) n d s) (g.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_move_stacks (5 : Fin 13) 8 (by decide)
    («stacks» (GCDMachine.outputState g) n d s) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (5 : Fin 13) 8) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [«stacks»,GCDMachine.outputState,
      reversedGCDWork,DivisionMachine.«stacks»,KS.W04.BinaryStackMoves.twoConfig]

theorem placeGCD_spec (g n d : List Bool) (s : Bool) :
    RunSpec placeGCD («stacks» (reversedGCDWork g) n d s)
      (divisorState g n d s) (g.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_move_stacks (8 : Fin 13) 2 (by decide)
    («stacks» (reversedGCDWork g) n d s) bits
    (by change bits.length=g.reverse.length+1; simpa only [List.length_reverse] using hlen)
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (8 : Fin 13) 2) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [«stacks»,divisorState,divisorWork,reversedGCDWork,
      DivisionMachine.«stacks»,KS.W04.BinaryStackMoves.twoConfig]

theorem computeGCD_spec (n d : List Bool) (s : Bool) (L : ℕ)
    (hnc : CanonicalBits n) (hdc : CanonicalBits d) (hn : n.length ≤ L) (hd : d.length ≤ L) :
    let g := Computability.encodeNat (Nat.gcd (bitsValue n) (bitsValue d))
    RunSpec computeGCD (state n d s) (divisorState g n d s)
      (120 * (L + 1) ^ 3) := by
  dsimp only
  let g := Computability.encodeNat (Nat.gcd (bitsValue n) (bitsValue d))
  have h := (prepare_spec n d s).compose ((gcd_spec n d s L hnc hdc hn hd).compose
    ((reverseGCD_spec g n d s).compose (placeGCD_spec g n d s)))
  have hg : g.length ≤ L := GCDMachine.gcd_encode_length_le n d L hn hd
  have hlin := Nat.le_self_pow (by decide : 3 ≠ 0) (L + 1)
  have ht : (3 * n.length + 2 * d.length + 5) +
      (100 * (L + 1) ^ 3 + ((g.length + 1) + (g.length + 1))) ≤ 120 * (L + 1) ^ 3 := by
    omega
  exact h.mono ht

end KS.W30.RationalMagnitudeMachine

end OAI
