import Mathlib
import OAI.Analysis.MatrixSigning.Machines.MachineCombinators

namespace OAI

section

namespace CurrentKS.FiniteControl
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

abbrev Registers (k : ℕ) := Fin k → List Bool

def guard {k : ℕ} (port : Fin k) (heads : Fin k → Fin 3) (_ : Bool) :
    KS.W29.FixedLoop.GuardInstruction k :=
  ⟨if (heads port).val = 0 then .halt else .call, Vector.ofFn (fun _ => .stay)⟩

def whileNonempty {k : ℕ} (port : Fin k) (body : Program k) : Program k :=
  KS.W29.FixedLoop.loop body (guard port)

lemma step_empty {k : ℕ} (port : Fin k) (body : Program k)
    (s : Registers k) (hs : s port = []) (coin : Bool) :
    (whileNonempty port body).toMachine.step
      ⟨some (whileNonempty port body).initial,s⟩ coin = ⟨none,s⟩ := by
  change (KS.W29.FixedLoop.loop body (guard port)).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState body),s⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  simp [guard, observedHeads, hs, KS.W29.topCode, KS.W29.FixedLoop.guardInstruction,
    KS.W01.FixedStack.Instruction.action, KS.W29.StackAction.apply]
  rfl

lemma step_nonempty {k : ℕ} (port : Fin k) (body : Program k)
    (s : Registers k) (hs : s port ≠ []) (coin : Bool) :
    (whileNonempty port body).toMachine.step
      ⟨some (whileNonempty port body).initial,s⟩ coin =
      KS.W29.FixedLoop.liftBody body ⟨some body.initial,s⟩ := by
  change (KS.W29.FixedLoop.loop body (guard port)).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState body),s⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  cases he : s port with
  | nil => exact (hs he).elim
  | cons b bs =>
    cases b <;> simp [guard, observedHeads, he, KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, KS.W29.FixedLoop.liftBody,
      KS.W01.FixedStack.Instruction.action, KS.W29.StackAction.apply] <;> rfl

inductive Trace {k : ℕ} (port : Fin k) (body : Program k) :
    Registers k → Registers k → ℕ → Prop
  | stop (s : Registers k) (hs : s port = []) : Trace port body s s 1
  | step {s t u : Registers k} {b c : ℕ} (hs : s port ≠ [])
      (hbody : RunSpec body s t b) (htail : Trace port body t u c) :
      Trace port body s u (b+c+1)

theorem run_trace {k : ℕ} {port : Fin k} {body : Program k}
    {s t : Registers k} {ticks : ℕ} (h : Trace port body s t ticks)
    (bits : List Bool) (hlen : ticks ≤ bits.length) :
    (whileNonempty port body).toMachine.run
      ⟨some (whileNonempty port body).initial,s⟩ bits = ⟨none,t⟩ := by
  induction h generalizing bits with
  | stop s hs =>
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      rw [KS.W01.FixedStack.Machine.run,step_empty port body s hs,KS.W01.FixedStack.Machine.run_halted _ _ rfl]
  | @step s t u b c hs hb ht ih =>
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      have hr : b+c ≤ rest.length := by simp only [List.length_cons] at hlen; omega
      obtain ⟨remaining,hlen',hreturn⟩ := hb.loop_body_then (guard port) rest (by omega)
      rw [KS.W01.FixedStack.Machine.run,step_nonempty port body s hs]
      change (KS.W29.FixedLoop.loop body (guard port)).toMachine.run
        (KS.W29.FixedLoop.liftBody body ⟨some body.initial,s⟩) rest = _
      rw [hreturn]
      exact ih remaining (by omega)

theorem trace_spec {k : ℕ} {port : Fin k} {body : Program k}
    {s t : Registers k} {ticks : ℕ} (h : Trace port body s t ticks) :
    RunSpec (whileNonempty port body) s t ticks := by
  intro bits hlen
  exact run_trace h bits hlen.ge

theorem sequence_spec {k : ℕ} (port : Fin k) (body : Program k)
    (states : ℕ → Registers k) (n B : ℕ)
    (hstop : states n port = [])
    (hstart : ∀ j < n, states j port ≠ [])
    (hbody : ∀ j < n, RunSpec body (states j) (states (j+1)) B) :
    RunSpec (whileNonempty port body) (states 0) (states n) (n*(B+1)+1) := by
  apply trace_spec
  induction n generalizing states with
  | zero => simpa using (Trace.stop (body := body) (states 0) hstop)
  | succ n ih =>
    have ht : Trace port body (states 1) (states (n+1)) (n*(B+1)+1) :=
      ih (fun j => states (j+1)) hstop
        (fun j hj => hstart (j+1) (by omega)) (fun j hj => hbody (j+1) (by omega))
    have he : B+(n*(B+1)+1)+1 = (n+1)*(B+1)+1 := by simp only [Nat.add_mul, Nat.one_mul]; omega
    rw [←he]
    exact Trace.step (hstart 0 (by omega)) (hbody 0 (by omega)) ht

end CurrentKS.FiniteControl

end

end OAI
