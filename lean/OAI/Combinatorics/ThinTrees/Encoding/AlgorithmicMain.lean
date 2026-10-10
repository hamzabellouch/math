import Mathlib
import OAI.Analysis.MatrixSigning.Realization.OriginalMachine
import OAI.Combinatorics.ThinTrees.Encoding.InputDispatch
import OAI.Combinatorics.ThinTrees.Sparsification.ExplicitAlgorithm

namespace OAI

/-! Algorithmic main. -/

section

namespace CurrentKS.Realization
open CleanRoutine
variable {α : Type*} {ea : α → Word} {f : α → Word}

def realizedMachine (r : Realizes ea wordCode f) : CurrentKS.Machine :=
  ArchivedMachine.machine ({r.routine.program with input := 0,output := 0}.toMachine)

lemma realizedMachine_run (r : Realizes ea wordCode f) (x : α) :
    (realizedMachine r).run (ea x) (r.cost x) = ⟨none,CleanRoutine.io (f x)⟩ := by
  let P := {r.routine.program with input := 0,output := 0}
  have h : KS.W03.MachineCombinators.RunSpec P (CleanRoutine.io (ea x))
      (CleanRoutine.io (f x)) (r.cost x) := by
    intro bits hb
    exact (CurrentKS.program_ports_run r.routine.program 0 0 _ bits).trans
      (r.routine.spec x bits hb)
  have ht := ArchivedMachine.runSpec_transfer P _ _ _ h
  change ((ArchivedMachine.machine P.toMachine).step^[r.cost x])
    ((ArchivedMachine.machine P.toMachine).init (ea x))=_
  have hi : (ArchivedMachine.machine P.toMachine).init (ea x) =
      ⟨some P.initial,CleanRoutine.io (ea x)⟩ := by
    apply congrArg (CurrentKS.Config.mk (some P.initial))
    refine funext (fun (j : Fin (r.routine.scratch+1)) => ?_)
    change (if j=(0 : Fin (r.routine.scratch+1)) then ea x else [])=
      (if j.val=0 then ea x else [])
    simp only [Fin.ext_iff,Fin.val_zero]
  rw [hi]
  exact ht
end CurrentKS.Realization

namespace AlgorithmicThinTrees.InputStack
open CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack

def machine (R : ℕ) : CurrentKS.Machine := realizedMachine (program R)

lemma machine_run (R : ℕ) (x : Good) :
    (machine R).run x.val.encode ((program R).cost x) =
      ⟨none,CurrentKS.CleanRoutine.io (output R x)⟩ :=
  realizedMachine_run (program R) x

lemma machine_correct {R : ℕ} {C : ℝ} (hC : 0<C)
    (hcorrect : ∀p : Problem,2≤p.d+1 → 1≤p.r → p.G.EdgeConnected p.r →
      ThinTree C p.r p.G (Iteration.tree R p.r p.G)) (x : Good) :
    let result := (machine R).run x.val.encode ((program R).cost x)
    result.state=none ∧ GoodOutput (2*C) x.val (result.stacks (machine R).outputStack) := by
  rw [machine_run]
  exact ⟨rfl,program_good hC hcorrect x⟩

end AlgorithmicThinTrees.InputStack

namespace AlgorithmicThinTrees
open CurrentKS.Realization KS.W23

theorem algorithmic_strong_thin_trees : AlgorithmicStrongThinTrees := by
  obtain ⟨R,C,hC,hcorrect,htime⟩ := Iteration.explicit_program
  have ht := InputStack.runsPoly_program htime (fun x : InputStack.Good => x)
    (isPoly_self (fun x : InputStack.Good => x.val.length))
  obtain ⟨p,hp⟩ := ht.cost
  refine ⟨2*C,by positivity,InputStack.machine R,p.coefficient+1,p.degree,Nat.succ_pos _,?_⟩
  intro x hx
  let y : InputStack.Good := ⟨x,hx⟩
  have hr := InputStack.machine_correct hC hcorrect y
  have hbound : (InputStack.program R).cost y ≤
      (p.coefficient+1)*(x.length+1)^p.degree :=
    ((hp y).trans (p.eval_le_input_polynomial x.length)).trans
      (Nat.mul_le_mul_right _ (Nat.le_succ p.coefficient))
  have he := CurrentKS.Machine.run_halted hr.1 hbound
  dsimp only [y] at he hr
  dsimp only
  rw [he]
  exact hr

end AlgorithmicThinTrees
end

end OAI
