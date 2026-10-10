import Mathlib
import OAI.Analysis.MatrixSigning.Machines.BisectionCommands

namespace OAI

namespace KS.W23.LiteralProgram
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def push {k : ℕ} (port : Fin k) (b : Bool) : Program k :=
  ofMachine (compile (0 : Fin 1) port port (fun _ _ _ =>
    ⟨none, Vector.ofFn (fun j => if j = port then .push b else .stay)⟩))

def pushAfter {k : ℕ} (port : Fin k) (b : Bool) (s : Fin k → List Bool) : Fin k → List Bool :=
  Function.update s port (b :: s port)

theorem push_spec {k : ℕ} (port : Fin k) (b : Bool) (s : Fin k → List Bool) :
    RunSpec (push port b) s (pushAfter port b s) 1 := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin rest =>
      have hr : rest = [] := List.length_eq_zero_iff.mp (by simpa using hbits)
      subst rest
      change (compile (0 : Fin 1) port port (fun _ _ _ =>
        ⟨none, Vector.ofFn (fun j => if j = port then .push b else .stay)⟩)).step
          ⟨some (0 : Fin 1), s⟩ coin = _
      rw [step_compile]
      apply congrArg (Config.mk none)
      funext j
      by_cases hj : j = port <;>
        simp [pushAfter, Function.update, Instruction.action, KS.W29.StackAction.apply, hj]

def program {k : ℕ} (port : Fin k) : List Bool → Program k
  | [] => W28.BisectionCommands.skip port
  | b :: bs => compose (program port bs) (push port b)

theorem program_spec {k : ℕ} (port : Fin k) (literal : List Bool) (s : Fin k → List Bool) :
    RunSpec (program port literal) s (Function.update s port (literal ++ s port))
      (literal.length + 1) := by
  induction literal with
  | nil => simpa [program] using W28.BisectionCommands.skip_spec port s
  | cons b bs ih =>
      have h := ih.compose (push_spec port b (Function.update s port (bs ++ s port)))
      simpa only [program, List.length_cons, pushAfter, Function.update_self,
        Function.update_idem, List.cons_append, Nat.add_assoc, Nat.add_comm 1 1] using h

def pop {k : ℕ} (port : Fin k) : Program k :=
  ofMachine (compile (0 : Fin 1) port port (fun _ _ _ =>
    ⟨none, Vector.ofFn (fun j => if j = port then .pop else .stay)⟩))

theorem pop_spec {k : ℕ} (port : Fin k) (s : Fin k → List Bool) :
    RunSpec (pop port) s (Function.update s port (s port).tail) 1 := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin rest =>
      have hr : rest = [] := List.length_eq_zero_iff.mp (by simpa using hbits)
      subst rest
      change (compile (0 : Fin 1) port port (fun _ _ _ =>
        ⟨none, Vector.ofFn (fun j => if j = port then .pop else .stay)⟩)).step
          ⟨some (0 : Fin 1), s⟩ coin = _
      rw [step_compile]
      apply congrArg (Config.mk none)
      funext j
      by_cases hj : j = port <;>
        simp [Function.update, Instruction.action, KS.W29.StackAction.apply, hj]

def dropProgram {k : ℕ} (port : Fin k) : ℕ → Program k
  | 0 => W28.BisectionCommands.skip port
  | n + 1 => compose (pop port) (dropProgram port n)

theorem drop_spec {k : ℕ} (port : Fin k) (n : ℕ) (s : Fin k → List Bool) :
    RunSpec (dropProgram port n) s (Function.update s port ((s port).drop n)) (n + 1) := by
  induction n generalizing s with
  | zero => simpa [dropProgram] using W28.BisectionCommands.skip_spec port s
  | succ n ih =>
      have h := (pop_spec port s).compose (ih (Function.update s port (s port).tail))
      have hd : ((s port).tail).drop n = (s port).drop (n + 1) := by
        cases hs : s port <;> simp
      simpa only [dropProgram, Function.update_self, Function.update_idem,
        hd, Nat.add_comm 1, Nat.add_assoc] using h

end KS.W23.LiteralProgram

end OAI
