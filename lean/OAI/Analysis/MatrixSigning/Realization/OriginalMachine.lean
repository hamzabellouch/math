import Mathlib
import OAI.Analysis.MatrixSigning.Realization.OriginalOutputRoutine
import OAI.Analysis.MatrixSigning.Realization.MachineAdapter

namespace OAI

namespace CurrentKS
open Realization CleanRoutine

def originalMachine : Machine :=
  ArchivedMachine.machine ({Realization.originalSigning.routine.program with input := 0,output := 0}.toMachine)

def originalMachineTicks : Input → ℕ := Realization.originalSigning.cost

lemma program_ports_run {k : ℕ} (P : KS.W29.FixedSequential.Program k) (a b : Fin k)
    (c : KS.W01.FixedStack.Config k P.states) (bits : List Bool) :
    ({P with input := a,output := b}.toMachine).run c bits=P.toMachine.run c bits := by
  induction bits generalizing c with
  | nil => rfl
  | cons bit bits ih =>
    have he : ({P with input := a,output := b}.toMachine).step c bit=P.toMachine.step c bit := by
      rcases c with ⟨s,ts⟩
      cases s <;> rfl
    simpa only [KS.W01.FixedStack.Machine.run,he] using ih (P.toMachine.step c bit)

lemma originalMachine_run (x : Input) :
    originalMachine.run x.encode (originalMachineTicks x)=
      ⟨none,CleanRoutine.io (RationalInput.signing x)⟩ := by
  let P := {Realization.originalSigning.routine.program with input := 0,output := 0}
  have h : KS.W03.MachineCombinators.RunSpec P (CleanRoutine.io x.encode)
      (CleanRoutine.io (RationalInput.signing x)) (originalMachineTicks x) :=
    by
      intro bits hb
      exact (program_ports_run Realization.originalSigning.routine.program 0 0 _ bits).trans
        (Realization.originalSigning.routine.spec x bits hb)
  have ht := ArchivedMachine.runSpec_transfer P _ _ _ h
  change ((ArchivedMachine.machine P.toMachine).step^[originalMachineTicks x])
    ((ArchivedMachine.machine P.toMachine).init x.encode)=_
  have hi : (ArchivedMachine.machine P.toMachine).init x.encode=
      ⟨some P.initial,CleanRoutine.io x.encode⟩ := by
    apply congrArg (Config.mk (some P.initial))
    refine funext (fun (j : Fin (originalSigning.routine.scratch+1)) => ?_)
    change (if j=(0 : Fin (originalSigning.routine.scratch+1)) then x.encode else [])=(if j.val=0 then x.encode else [])
    simp only [Fin.ext_iff,Fin.val_zero]
  rw [hi]
  exact ht

lemma Machine.run_halted {M : Machine} {input : List Bool} {k t : ℕ}
    (h : (M.run input k).state=none) (ht : k≤t) : M.run input t=M.run input k := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [Nat.add_comm k r,Machine.run,Function.iterate_add_apply,←Machine.run]
  apply Function.iterate_fixed
  simp only [Machine.step,h]

theorem originalMachine_correct (x : Input) (hx : Admissible x) :
    let result := originalMachine.run x.encode (originalMachineTicks x)
    result.state=none ∧ GoodOutput x (result.«stacks» originalMachine.outputStack) := by
  rw [originalMachine_run]
  exact ⟨rfl,Realization.originalSigning_good x hx⟩

lemma deterministic_of_original_cost
    (h : ∃ C degree : ℕ,0<C ∧ ∀ x,Admissible x →
      originalMachineTicks x≤C*(x.length+1)^degree) : DeterministicRankOneSigning := by
  obtain ⟨C,k,hC,h⟩ := h
  refine ⟨originalMachine,C,k,hC,?_⟩
  intro x hx
  have hc := originalMachine_correct x hx
  have he := Machine.run_halted hc.1 (h x hx)
  simpa only [he] using hc

end CurrentKS

end OAI
