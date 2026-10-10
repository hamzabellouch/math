import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderRun
import OAI.MathematicalPhysics.NavierStokes.Material.Machines

namespace OAI

/-! The seven-row recorder applied to finite machine tables. -/

namespace ForcedComputation.Recorder

def ofMachine (M : Alternating.Machine) : Machine ℕ ℕ where
  halting := M.isHalting
  next := fun q a => (M.normalizedInstruction q a).1
  write := fun q a => (M.normalizedInstruction q a).2.1
  move := fun q a => ((M.normalizedInstruction q a).2.2.val : ℤ) - 1
  move_bound := by
    intro q a
    have h := (M.normalizedInstruction q a).2.2.isLt
    constructor <;> omega

def originalConfiguration (C : Alternating.Configuration) : WorkConfiguration ℕ ℕ :=
  ⟨C.state, C.head, C.tape⟩

theorem originalConfiguration_step (M : Alternating.Machine) (C : Alternating.Configuration) :
    originalConfiguration (M.step C) = workNext (ofMachine M) (originalConfiguration C) := by
  rw [M.step_eq_normalized]
  simp only [originalConfiguration, Alternating.applyInstruction, workNext, ofMachine,
    sub_eq_add_neg, add_assoc]

theorem workAt_ofMachine (I : Alternating.MachineInput) (n : ℕ) :
    workAt (ofMachine I.1) 0 (Alternating.initialConfiguration I.2).tape n =
      originalConfiguration (Alternating.configurationAt I n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [workAt_succ, Alternating.configurationAt_succ, originalConfiguration_step, ih]

def initializedRecorder (I : Alternating.MachineInput) : Configuration ℕ ℕ :=
  checkpointAt (ofMachine I.1) 0 (Alternating.initialConfiguration I.2).tape 2 0

/-- The recorder's finite initialized run has exactly the original machine's
halting event, including a machine initially in a halting state. -/
theorem recorder_halts_iff (I : Alternating.MachineInput) :
    (∃ m C q, Steps (ofMachine I.1) m (initializedRecorder I) C ∧
      C.control = Control.checkpoint q ∧ I.1.isHalting q = true) ↔ Alternating.Halts I := by
  change (∃ m C q, Steps (ofMachine I.1) m
    (checkpointAt (ofMachine I.1) 0 (Alternating.initialConfiguration I.2).tape 2 0) C ∧
      C.control = Control.checkpoint q ∧ (ofMachine I.1).halting q = true) ↔ _
  rw [halting_checkpoint_iff _ _ _ 2 (by norm_num)]
  change (∃ n, I.1.isHalting
    (workAt (ofMachine I.1) 0 (Alternating.initialConfiguration I.2).tape n).state = true) ↔ _
  simp only [workAt_ofMachine, originalConfiguration, Alternating.Halts]

end ForcedComputation.Recorder

end OAI
