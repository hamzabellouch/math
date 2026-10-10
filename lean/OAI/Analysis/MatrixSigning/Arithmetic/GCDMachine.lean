import Mathlib
import OAI.Analysis.MatrixSigning.Machines.MachineCombinators
import OAI.Analysis.MatrixSigning.Arithmetic.DivisionMachine

namespace OAI

section

namespace KS.W30.GCDMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

def clearQuotient : Program 10 := KS.W04.BinaryStackMoves.clearProgram 5
def advanceDividend : Program 10 := KS.W04.BinaryStackMoves.moveProgram 2 3
def reverseRemainder : Program 10 := KS.W04.BinaryStackMoves.moveProgram 4 8
def remainderPorts : Fin 3 ↪ Fin 10 := ⟨![0,2,8], by decide⟩
def trimRemainder : Program 10 := ofMachine (lift3 BinaryTrimMachine.machine remainderPorts)
def cleanup : Program 10 := compose clearQuotient
  (compose advanceDividend (compose reverseRemainder trimRemainder))
def body : Program 10 := compose DivisionMachine.loop cleanup

def guard (heads : Fin 10 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 10 :=
  ⟨if (heads 2).val = 0 then .halt else .call, Vector.ofFn (fun _ => .stay)⟩
def loop : Program 10 := KS.W29.FixedLoop.loop body guard

def finish : Program 10 := KS.W04.BinaryStackMoves.moveProgram 3 5
def program : Program 10 := compose loop finish

def state (a b : List Bool) : Fin 10 → List Bool :=
  DivisionMachine.«stacks» b a.reverse [] [] [] [] [] []

theorem clearQuotient_spec (d q r : List Bool) :
    RunSpec clearQuotient (DivisionMachine.«stacks» d [] q r [] [] [] [])
      (DivisionMachine.«stacks» d [] [] r [] [] [] []) (q.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_clear_stacks (5 : Fin 10)
    (DivisionMachine.«stacks» d [] q r [] [] [] []) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.clearMachine (5 : Fin 10)) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem advanceDividend_spec (d r : List Bool) :
    RunSpec advanceDividend (DivisionMachine.«stacks» d [] [] r [] [] [] [])
      (DivisionMachine.«stacks» [] d.reverse [] r [] [] [] []) (d.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_move_stacks (2 : Fin 10) 3 (by decide)
    (DivisionMachine.«stacks» d [] [] r [] [] [] []) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (2 : Fin 10) 3) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [DivisionMachine.«stacks», KS.W04.BinaryStackMoves.twoConfig]

theorem reverseRemainder_spec (pending r : List Bool) :
    RunSpec reverseRemainder (DivisionMachine.«stacks» [] pending [] r [] [] [] [])
      (DivisionMachine.«stacks» [] pending [] [] [] [] r.reverse []) (r.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_move_stacks (4 : Fin 10) 8 (by decide)
    (DivisionMachine.«stacks» [] pending [] r [] [] [] []) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (4 : Fin 10) 8) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [DivisionMachine.«stacks», KS.W04.BinaryStackMoves.twoConfig]

theorem trimRemainder_start (pending r : List Bool) :
    (⟨some trimRemainder.initial, DivisionMachine.«stacks» [] pending [] [] [] [] r.reverse []⟩ :
      Config 10 trimRemainder.states) =
      pack remainderPorts (BinaryTrimMachine.cfg (some 0) [] [] r.reverse)
        (DivisionMachine.«stacks» [] pending [] [] [] [] [] []) := by
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem trimRemainder_spec (pending r : List Bool) :
    RunSpec trimRemainder (DivisionMachine.«stacks» [] pending [] [] [] [] r.reverse [])
      (DivisionMachine.«stacks» (trimBits r) pending [] [] [] [] [] []) (r.length + 1) := by
  intro bits hlen
  erw [trimRemainder_start]
  refine (KS.W19.MachineTransport.run_ofMachine
    (lift3 BinaryTrimMachine.machine remainderPorts) _ bits).trans ?_
  refine (run_pack BinaryTrimMachine.machine remainderPorts _ _ bits).trans ?_
  refine (congrArg (fun c => pack remainderPorts c
    (DivisionMachine.«stacks» [] pending [] [] [] [] [] []))
    (BinaryTrimMachine.run_trim [] [] r.reverse bits
      (by simpa only [List.length_reverse] using hlen))).trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp only [List.reverse_reverse, List.append_nil] <;> rfl

theorem cleanup_spec (d q r : List Bool) :
    RunSpec cleanup (DivisionMachine.«stacks» d [] q r [] [] [] [])
      (state d (trimBits r)) (q.length + d.length + 2 * r.length + 4) := by
  have h := (clearQuotient_spec d q r).compose
    ((advanceDividend_spec d r).compose
      ((reverseRemainder_spec d.reverse r).compose (trimRemainder_spec d.reverse r)))
  have ht : (q.length+1)+((d.length+1)+((r.length+1)+(r.length+1))) =
      q.length+d.length+2*r.length+4 := by omega
  rw [ht] at h
  exact h

theorem loop_table_length : loop.table.length = (body.states + 1) * (3 ^ 10 * 2) :=
  KS.W29.FixedLoop.loop_table_length body guard

end KS.W30.GCDMachine

end

end OAI
