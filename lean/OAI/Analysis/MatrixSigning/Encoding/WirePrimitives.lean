import Mathlib
import OAI.Analysis.MatrixSigning.Machines.StackTransferSpecs
import OAI.Analysis.MatrixSigning.Machines.FixedCopyRestore
import OAI.Analysis.MatrixSigning.Machines.FixedRun

namespace OAI

namespace KS.W20.Wire
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

variable {k : ℕ}

def pushDispatch (port : Fin k) (value : Bool) (_ : Fin 1)
    (_ : Fin k → Fin 3) (_ : Bool) : Instruction k 1 :=
  ⟨none, Vector.ofFn (fun j => if j = port then .push value else .stay)⟩

def push (port : Fin k) (value : Bool) : Program k :=
  ofMachine (compile 0 port port (pushDispatch port value))

theorem push_spec (port : Fin k) (value : Bool) (before : Fin k → List Bool) :
    RunSpec (push port value) before (Function.update before port (value :: before port)) 1 := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin tail =>
    have ht : tail = [] := by apply List.length_eq_zero_iff.mp; simpa using hbits
    subst tail
    rw [Machine.run]
    change (compile (0 : Fin 1) port port (pushDispatch port value)).step
      ⟨some (0 : Fin 1), before⟩ coin = _
    rw [step_compile]
    apply KS.W19.FixedRun.config_ext
    · rfl
    · intro j
      by_cases hj : j = port <;>
        simp [pushDispatch, Instruction.action, KS.W29.StackAction.apply, Function.update, hj]

def halt (port : Fin k) : Program k :=
  ofMachine (compile (0 : Fin 1) port port (fun _ _ _ => Instruction.halt k 1))

theorem halt_spec (port : Fin k) (before : Fin k → List Bool) :
    RunSpec (halt port) before before 1 := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin tail =>
    have ht : tail = [] := by apply List.length_eq_zero_iff.mp; simpa using hbits
    subst tail
    rw [Machine.run]
    change (compile (0 : Fin 1) port port (fun _ _ _ => Instruction.halt k 1)).step
      ⟨some (0 : Fin 1), before⟩ coin = _
    rw [step_compile]
    apply KS.W19.FixedRun.config_ext
    · rfl
    · intro j
      simp [Instruction.halt, Instruction.action, KS.W29.StackAction.apply]

def writeBits (port : Fin k) : List Bool → Program k
  | [] => halt port
  | b :: bs => compose (writeBits port bs) (push port b)

theorem writeBits_spec (port : Fin k) (xs : List Bool) (before : Fin k → List Bool) :
    RunSpec (writeBits port xs) before
      (Function.update before port (xs ++ before port)) (xs.length + 1) := by
  induction xs with
  | nil =>
      simpa only [writeBits, List.nil_append, List.length_nil, Nat.zero_add,
        Function.update_eq_self] using halt_spec port before
  | cons b bs ih =>
      have h := ih.compose (push_spec port b (Function.update before port (bs ++ before port)))
      convert h using 1 <;> (try rfl)
      · funext j
        by_cases hj : j = port <;> simp [Function.update, hj]

theorem copy_spec (ports : Fin 3 ↪ Fin k) (before : Fin k → List Bool)
    (hdst : before (ports 1) = []) (hscratch : before (ports 2) = []) :
    RunSpec (KS.W01.FixedCopy.program ports) before
      (Function.update before (ports 1) (before (ports 0)))
      (2 * (before (ports 0)).length + 2) := by
  intro bits hbits
  exact KS.W01.FixedCopy.run_copy_restore ports before (before (ports 0)) bits
    rfl hdst hscratch hbits

def transfer (source target scratch : Fin k) : Program k :=
  compose (KS.W04.BinaryStackMoves.moveProgram source scratch)
    (KS.W04.BinaryStackMoves.moveProgram scratch target)

def transferAfter (source target : Fin k) (before : Fin k → List Bool) : Fin k → List Bool :=
  fun j => if j = source then [] else if j = target then before source else before j

theorem transfer_spec (source target scratch : Fin k)
    (hst : source ≠ target) (hsc : source ≠ scratch) (hct : scratch ≠ target)
    (before : Fin k → List Bool) (ht : before target = []) (hc : before scratch = []) :
    RunSpec (transfer source target scratch) before (transferAfter source target before)
      (2 * (before source).length + 2) := by
  have h₁ := KS.W15.RationalMultiply.move_spec source scratch hsc before
  have h₂ := KS.W15.RationalMultiply.move_spec scratch target hct
    (KS.W15.RationalMultiply.moveAfter source scratch before)
  have h := h₁.compose h₂
  convert h using 1 <;> (try rfl)
  · funext j
    by_cases hs : j = source
    · subst j
      simp [KS.W15.RationalMultiply.moveAfter, transferAfter, hsc, hst]
    · by_cases hj : j = target
      · subst j
        simp [KS.W15.RationalMultiply.moveAfter, transferAfter, Ne.symm hst,
          Ne.symm hsc, Ne.symm hct, ht, hc]
      · by_cases htemp : j = scratch
        · subst j
          simp [KS.W15.RationalMultiply.moveAfter, transferAfter, Ne.symm hsc, hct, hc]
        · simp [KS.W15.RationalMultiply.moveAfter, transferAfter, hs, hj, htemp]
  · simp [KS.W15.RationalMultiply.moveAfter, Ne.symm hsc, hc]; omega

end KS.W20.Wire

end OAI
