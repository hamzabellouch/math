import Mathlib
import OAI.Combinatorics.ThinTrees.Encoding.GreedyRealization

namespace OAI

/-! Word head. -/

section

namespace CurrentKS.WordHead
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine PairRoutine

def dispatch (_ : Fin 1) (heads : Fin 3 → Fin 3) (_ : Bool) : KS.W01.FixedStack.Instruction 3 1 :=
  ⟨none,Vector.ofFn (fun j => if j=1 then .push (decide (heads 0=2)) else .stay)⟩
def flag : Program 3 := ofMachine (compile 0 0 1 dispatch)
def program : Program 3 := compose flag (compose (KS.W04.BinaryStackMoves.clearProgram 0)
  (transfer 1 2 0))
lemma flag_spec (w : Word) : RunSpec flag (io w) (smallState w [w.headD false] []) 1 := by
  intro bits hbits
  obtain ⟨coin,rfl⟩ := List.length_eq_one_iff.mp hbits
  change (compile (0 : Fin 1) 0 1 dispatch).step ⟨some (0 : Fin 1),io w⟩ coin=_
  rw [step_compile]
  apply KS.W19.FixedRun.config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [dispatch,KS.W01.FixedStack.Instruction.action,KS.W29.StackAction.apply,
      io,smallState,observedHeads]
    cases w with
    | nil => rfl
    | cons b bs => cases b <;> rfl

def routine : Routine (fun w : Word => w) (fun w => [w.headD false]) (fun w => w.length+6) where
  scratch := 2
  program := program
  spec w := by
    have h := (flag_spec w).compose ((PairRoutine.clear_first [w.headD false] w).compose
      (PairRoutine.take_first [w.headD false]))
    convert h using 1 <;> (try rfl)
    simp
    omega
end CurrentKS.WordHead

namespace CurrentKS.Realization
open CleanRoutine KS.W23
def wordHead : Realizes wordCode boolCode (fun w => w.headD false) where
  cost := fun w => w.length+6
  routine := WordHead.routine
instance poly_wordHead : PolyTime wordHead := ⟨⟨NaturalPolynomial.variable+6,fun _ => le_rfl⟩⟩
end CurrentKS.Realization
end

end OAI
