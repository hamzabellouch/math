import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedCompare
import OAI.Analysis.MatrixSigning.Arithmetic.BisectionArithmetic

namespace OAI

section

namespace KS.W28.BisectionCommands
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W28.BisectionArithmetic

inductive Call (k : ℕ) where
  | copy (ports : Fin 3 ↪ Fin k)
  | clear (port : Fin k)
  | add (ports : Fin 3 ↪ Fin k)
  | multiply (ports : Fin 7 ↪ Fin k)
  | compare (ports : Fin 3 ↪ Fin k)
  | shift (a b : Fin k)

def Call.program {k : ℕ} : Call k → Program k
  | .copy ports => KS.W01.FixedCopy.program ports
  | .clear port => KS.W04.BinaryStackMoves.clearProgram port
  | .add ports => addProgram ports
  | .multiply ports => productProgram ports
  | .compare ports => FixedCompare.program ports
  | .shift a b => shiftProgram a b

def Call.eval {k : ℕ} : Call k → Workspace k → Workspace k
  | .copy ports, s => Function.update s (ports 1) (s (ports 0))
  | .clear port, s => clearAfter port s
  | .add ports, s => addAfter ports s
  | .multiply ports, s => productAfter ports s
  | .compare ports, s => FixedCompare.after ports s
      (decide (KS.W19.bitsValue (s (ports 0)) ≤ KS.W19.bitsValue (s (ports 1))))
  | .shift a b, s => shiftAfter a b s

def Call.ready {k : ℕ} : Call k → Workspace k → Prop
  | .copy ports, s => s (ports 1) = [] ∧ s (ports 2) = []
  | .clear _, _ => True
  | .add ports, s => s (ports 2) = []
  | .multiply ports, s => s (ports 3) = [] ∧ s (ports 4) = [] ∧
      s (ports 5) = [] ∧ s (ports 6) = []
  | .compare _, _ => True
  | .shift _ _, _ => True

def Call.ticks {k : ℕ} : Call k → Workspace k → ℕ
  | .copy ports, s => 2 * (s (ports 0)).length + 2
  | .clear port, s => (s port).length + 1
  | .add ports, s => 2 * max (s (ports 0)).length (s (ports 1)).length + 3
  | .multiply ports, s => 17 * ((s (ports 1)).length + (s (ports 2)).length + 2) ^ 2
  | .compare ports, s => max (s (ports 0)).length (s (ports 1)).length + 1
  | .shift _ _, _ => 1

theorem Call.spec {k : ℕ} (a : Call k) (s : Workspace k) (h : a.ready s) :
    RunSpec a.program s (a.eval s) (a.ticks s) := by
  cases a with
  | copy ports => exact copy_spec ports s h.1 h.2
  | clear port => exact clear_spec port s
  | add ports => exact add_spec_stacks ports s h
  | multiply ports => exact product_spec ports s h.1 h.2.1 h.2.2.1 h.2.2.2
  | compare ports => exact FixedCompare.compare_spec ports s
  | shift a b => exact shift_spec a b s

def skip {k : ℕ} (port : Fin k) : Program k :=
  ofMachine (compile (0 : Fin 1) port port
    (fun _ _ _ => ⟨none, Vector.ofFn (fun _ => .stay)⟩))

theorem skip_spec {k : ℕ} (port : Fin k) (s : Workspace k) : RunSpec (skip port) s s 1 := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons b bs =>
      have hb : bs = [] := List.length_eq_zero_iff.mp (by simpa using hbits)
      subst bs
      change (compile (0 : Fin 1) port port
        (fun _ _ _ => ⟨none, Vector.ofFn (fun _ => .stay)⟩)).step ⟨some (0 : Fin 1), s⟩ b = _
      rw [step_compile]
      apply congrArg (Config.mk none)
      funext j
      simp [Instruction.action, KS.W29.StackAction.apply]

def program {k : ℕ} (port : Fin k) : List (Call k) → Program k
  | [] => skip port
  | a :: as => compose a.program (program port as)

def eval {k : ℕ} : List (Call k) → Workspace k → Workspace k
  | [], s => s
  | a :: as, s => eval as (a.eval s)

def ready {k : ℕ} : List (Call k) → Workspace k → Prop
  | [], _ => True
  | a :: as, s => a.ready s ∧ ready as (a.eval s)

def ticks {k : ℕ} : List (Call k) → Workspace k → ℕ
  | [], _ => 1
  | a :: as, s => a.ticks s + ticks as (a.eval s)

theorem sequence_spec {k : ℕ} (port : Fin k) (calls : List (Call k))
    (s : Workspace k) (h : ready calls s) :
    RunSpec (program port calls) s (eval calls s) (ticks calls s) := by
  induction calls generalizing s with
  | nil => exact skip_spec port s
  | cons a as ih => exact (a.spec s h.1).compose (ih (a.eval s) h.2)

end KS.W28.BisectionCommands

end

end OAI
