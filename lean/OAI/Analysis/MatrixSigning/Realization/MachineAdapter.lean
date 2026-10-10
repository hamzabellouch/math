import Mathlib
import OAI.Analysis.MatrixSigning.Model
import OAI.Analysis.MatrixSigning.Machines.MachineCombinators

namespace OAI

namespace CurrentKS.ArchivedMachine
open KS.W01.FixedStack

def action : KS.W29.StackAction → CurrentKS.StackAction
  | .stay => .stay
  | .pop => .pop
  | .push b => .push b

def instruction {k q : ℕ} (a : KS.W01.FixedStack.Instruction k q) :
    CurrentKS.Instruction k q := ⟨a.next,fun j => action (a.action j)⟩

lemma action_apply (a : KS.W29.StackAction) (l : List Bool) :
    (action a).apply l=a.apply l := by cases a <;> rfl

def machine (M : KS.W01.FixedStack.Machine) : CurrentKS.Machine where
  stackCount := M.stackCount
  states := M.states
  initial := M.initial
  inputStack := M.inputStack
  outputStack := M.outputStack
  table := List.ofFn fun i : Fin (M.states*3^M.stackCount) =>
    instruction (M.table.getD (2*i.val) (KS.W01.FixedStack.Instruction.halt _ _))

def config {k q : ℕ} (c : KS.W01.FixedStack.Config k q) : CurrentKS.Config k q :=
  ⟨c.state,c.«stacks»⟩

lemma heads_eq (k : ℕ) (s : Fin k → List Bool) :
    KS.W01.FixedStack.headsCode k (fun j => ⟨KS.W29.topCode (s j),KS.W29.topCode_lt_three _⟩)=
      CurrentKS.headsCode k s := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [KS.W01.FixedStack.headsCode,CurrentKS.headsCode,ih]
      rfl

lemma heads_lt (k : ℕ) (s : Fin k → List Bool) : CurrentKS.headsCode k s<3^k := by
  rw [←heads_eq]
  exact KS.W01.FixedStack.headsCode_lt _ _

lemma step_eq (M : KS.W01.FixedStack.Machine) (c : KS.W01.FixedStack.Config M.stackCount M.states) :
    (machine M).step (config c)=config (M.step c false) := by
  rcases c with ⟨s,ts⟩
  cases s with
  | none => rfl
  | some q =>
      have hi : 3^M.stackCount*q.val+CurrentKS.headsCode M.stackCount ts<
          M.states*3^M.stackCount := by
        have hh := heads_lt M.stackCount ts
        have hq := q.isLt
        nlinarith
      have hl : 3^M.stackCount*q.val+CurrentKS.headsCode M.stackCount ts<
          (List.ofFn fun i : Fin (M.states*3^M.stackCount) =>
            instruction (M.table.getD (2*i.val) (KS.W01.FixedStack.Instruction.halt _ _))).length := by
        simpa only [List.length_ofFn] using hi
      simp only [CurrentKS.Machine.step,machine,config,List.getD_eq_getElem _ _ hl,
        List.getElem_ofFn,KS.W01.FixedStack.Machine.step]
      rw [KS.W01.FixedStack.tableIndex_val]
      have hh : KS.W01.FixedStack.headsCode M.stackCount
          (KS.W01.FixedStack.observedHeads (⟨some q,ts⟩ : KS.W01.FixedStack.Config _ _))=
          CurrentKS.headsCode M.stackCount ts := heads_eq _ _
      rw [hh]
      simp only [KS.W29.bitCode,Bool.false_eq_true,↓reduceIte,add_zero]
      have he : 3^M.stackCount*2*q.val+2*CurrentKS.headsCode M.stackCount ts=
          2*(3^M.stackCount*q.val+CurrentKS.headsCode M.stackCount ts) := by ring
      rw [he]
      unfold instruction
      congr 1
      funext j
      exact action_apply _ _

lemma iterate_eq (M : KS.W01.FixedStack.Machine) (k : ℕ)
    (c : KS.W01.FixedStack.Config M.stackCount M.states) :
    ((machine M).step^[k]) (config c)=config (M.run c (List.replicate k false)) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply,step_eq]
      exact ih (M.step c false)

lemma init_eq (M : KS.W01.FixedStack.Machine) (input : List Bool) :
    (machine M).init input=config (M.init input) := rfl

theorem run_eq (M : KS.W01.FixedStack.Machine) (input : List Bool) (fuel : ℕ) :
    (machine M).run input fuel=config (M.run (M.init input) (List.replicate fuel false)) := by
  rw [CurrentKS.Machine.run,init_eq]
  exact iterate_eq M fuel (M.init input)

theorem runSpec_transfer {k : ℕ} (P : KS.W29.FixedSequential.Program k)
    (before after : Fin k → List Bool) (ticks : ℕ)
    (h : KS.W03.MachineCombinators.RunSpec P before after ticks) :
    ((machine P.toMachine).step^[ticks]) (⟨some P.initial,before⟩ : CurrentKS.Config k P.states)=
      ⟨none,after⟩ := by
  have hr := h (List.replicate ticks false) (List.length_replicate ..)
  have hi := iterate_eq P.toMachine ticks ⟨some P.initial,before⟩
  rw [hr] at hi
  exact hi

end CurrentKS.ArchivedMachine

end OAI
