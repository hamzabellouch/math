import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.FiniteStore
import OAI.Combinatorics.MatchingCount.Arithmetic.BinarySubtract

namespace OAI

namespace MatchingFPRAS.ForwardSubtract
open Turing MachineCost StackAddition StackSubtract

local instance initialControl : Inhabited (Bool⊕Unit) := ⟨.inl false⟩
abbrev Γ := fun _ : Fin 3 => Bool
def program : Bool⊕Unit → TM2.Stmt Γ (Bool⊕Unit) Store :=
  StackComposition.sequence StackSubtract.program ForwardAddition.reverseProgram
lemma run_sub (A B : List Bool) :
    ∃ k≤2*(A.length+B.length)+2,
      MachineCost.run (TM2.step program) k ⟨some default,default,stackData A B []⟩=
        ⟨none,default,stackData ((subDigits false A B).2) [] []⟩ := by
  obtain ⟨n,hn,he⟩:=run_subtraction A B [] false default
  have he' : MachineCost.run (TM2.step StackSubtract.program) n
      (StackSubtract.cfg (some false) A B [] default)=StackSubtract.cfg none [] [] ((subDigits false A B).2).reverse default := by
    simpa only [List.append_nil] using he
  have hr := ForwardAddition.run_reverse [] [] ((subDigits false A B).2).reverse default
  have hr' : MachineCost.run (TM2.step ForwardAddition.reverseProgram) (((subDigits false A B).2).length+1)
      ⟨some default,default,stackData [] [] ((subDigits false A B).2).reverse⟩=
      ⟨none,default,stackData ((subDigits false A B).2) [] []⟩ := by
    simpa only [ForwardAddition.rcfg,List.length_reverse,List.reverse_reverse,List.append_nil] using hr
  obtain ⟨k,hk,hkrun⟩:=StackComposition.sequence_run StackSubtract.program ForwardAddition.reverseProgram
    (StackSubtract.cfg (some false) A B [] default) n (((subDigits false A B).2).length+1)
    (default : Store) (default : Store) (stackData [] [] ((subDigits false A B).2).reverse)
      (stackData ((subDigits false A B).2) [] []) he' hr'
  refine ⟨k,?_,?_⟩
  · have hl:=subDigits_length A B false
    omega
  · exact hkrun
end MatchingFPRAS.ForwardSubtract

namespace MatchingFPRAS.BinaryArithmeticProc
open RegisterProc Turing

local instance subEntry : Inhabited (Bool⊕Unit) := ⟨.inl false⟩
def sub : Proc (Fin 3) := FiniteStore.procedure ForwardSubtract.program (default : StackAddition.Store)
lemma sub_exec (A B : List Bool) :
    Exec sub ![A,B,[]] ![(StackSubtract.subDigits false A B).2,[],[]] (2*(A.length+B.length)+2) := by
  obtain ⟨n,hn,he⟩:=ForwardSubtract.run_sub A B
  exact (FiniteStore.exec ForwardSubtract.program default default _ _ n he).mono hn
end MatchingFPRAS.BinaryArithmeticProc

end OAI
