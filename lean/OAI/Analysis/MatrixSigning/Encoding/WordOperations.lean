import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedRun
import OAI.Analysis.MatrixSigning.Realization.PairRoutine

namespace OAI

namespace CurrentKS.WordOperations
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine PairRoutine

def appendProgram : Program 3 := compose split (KS.W12.StackTransfer.program 1 0 2)
def appending : Routine (fun p : Word×Word => pair p.1 p.2) (fun p => p.1++p.2)
    (fun p => 5*p.1.length+4) where
  scratch := 2
  program := appendProgram
  spec p := by
    have h := KS.W12.StackTransfer.spec (1 : Fin 3) 0 2 (by decide) (by decide) (by decide)
      (smallState p.2 p.1 []) rfl
    have he : KS.W12.StackTransfer.after 1 0 (smallState p.2 p.1 [])=io (p.1++p.2) := by
      funext j;fin_cases j <;> simp [KS.W12.StackTransfer.after,smallState,io]
    rw [he] at h
    have h' := (split_spec p.1 p.2).compose h
    convert h' using 1 <;> (try rfl)
    simp [smallState]
    omega

def emptyDispatch (_ : Fin 1) (heads : Fin 3 → Fin 3) (_ : Bool) : KS.W01.FixedStack.Instruction 3 1 :=
  ⟨none,Vector.ofFn (fun j => if j=1 then .push (decide (heads 0=0)) else .stay)⟩
def emptyFlag : Program 3 := ofMachine (compile 0 0 1 emptyDispatch)
def emptyProgram : Program 3 := compose emptyFlag (compose (KS.W04.BinaryStackMoves.clearProgram 0)
  (transfer 1 2 0))

lemma emptyFlag_spec (w : Word) : RunSpec emptyFlag (io w) (smallState w [w.isEmpty] []) 1 := by
  intro bits hbits
  obtain ⟨coin,rfl⟩ := List.length_eq_one_iff.mp hbits
  change (compile (0 : Fin 1) 0 1 emptyDispatch).step ⟨some (0 : Fin 1),io w⟩ coin=_
  rw [step_compile]
  apply KS.W19.FixedRun.config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [emptyDispatch,KS.W01.FixedStack.Instruction.action,KS.W29.StackAction.apply,io,smallState,
      observedHeads]
    cases w with
    | nil => rfl
    | cons b bs => cases b <;> rfl

def isEmpty : Routine (fun w : Word => w) (fun w => [w.isEmpty]) (fun w => w.length+6) where
  scratch := 2
  program := emptyProgram
  spec w := by
    have h := (emptyFlag_spec w).compose ((PairRoutine.clear_first [w.isEmpty] w).compose
      (PairRoutine.take_first [w.isEmpty]))
    convert h using 1 <;> (try rfl)
    simp
    omega

end CurrentKS.WordOperations

end OAI
