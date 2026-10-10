import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreePostRealization

namespace OAI

namespace MatchingFPRAS.RegisterProc
open Turing MachineCost

variable {K : Type} [DecidableEq K]
lemma Exec.unique {P : Proc K} {S T U : Stack K} {m n : ℕ}
    (h : Exec P S T m) (g : Exec P S U n) : T=U := by
  obtain ⟨i,hi,he⟩:=h
  obtain ⟨j,hj,hf⟩:=g
  have h₁ : MachineCost.run (TM2.step P.code) (i+j) ⟨some default,none,S⟩=⟨none,none,T⟩ := by
    rw [run_add,he,StackComposition.run_halted]
  have h₂ : MachineCost.run (TM2.step P.code) (i+j) ⟨some default,none,S⟩=⟨none,none,U⟩ := by
    rw [Nat.add_comm,run_add,hf,StackComposition.run_halted]
  exact congrArg TM2.Cfg.stk (h₁.symm.trans h₂)
end MatchingFPRAS.RegisterProc

namespace MatchingFPRAS.TreePost
open TreeTyped TreeData TreeFunction TreeMachine RegisterProc

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]
lemma stacks_eq_of_encode {a : A} {b : B} (h : TreeTyped.encode a=TreeTyped.encode b) :
    inputStacks a=inputStacks b := by simp only [inputStacks,h]
lemma packed_eq_of_stacks {a : A} {b : B} (h : inputStacks a=inputStacks b) : packed a=packed b := by
  have hw : weight a=weight b := by
    have hh:=congrFun h (.inl 0)
    change (TreeData.encode (TreeTyped.encode a)).length=(TreeData.encode (TreeTyped.encode b)).length
    exact congrArg List.length hh
  simp only [packed,h,hw]
lemma packed_eq_of_encode {a : A} {b : B} (h : TreeTyped.encode a=TreeTyped.encode b) : packed a=packed b :=
  packed_eq_of_stacks (stacks_eq_of_encode h)
lemma sameProgram_output {f : A→B} {g : C→D} (F : Realizer f) (G : Realizer g)
    (h : F.program=G.program) (a : A) (b : C) (hi : TreeTyped.encode a=TreeTyped.encode b) :
    packed (f a)=packed (g b) := by
  have hf:=F.correct a .nil
  have hg:=G.correct b .nil
  change Exec F.program (inputStacks a) (inputStacks (f a)) _ at hf
  change Exec G.program (inputStacks b) (inputStacks (g b)) _ at hg
  rw [h,stacks_eq_of_encode hi] at hf
  exact packed_eq_of_stacks (hf.unique hg)
end MatchingFPRAS.TreePost

end OAI
