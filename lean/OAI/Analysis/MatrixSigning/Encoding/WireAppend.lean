import Mathlib
import OAI.Analysis.MatrixSigning.Machines.MachineCombinators
import OAI.Analysis.MatrixSigning.Machines.BinaryStackMoves

namespace OAI

section

namespace KS.W07.WireAppend

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def moveAfter {k : ℕ} (source target : Fin k) (before : Fin k → List Bool) : Fin k → List Bool :=
  fun j => if j=source then [] else if j=target then (before source).reverse ++ before target else before j

theorem move_spec {k : ℕ} (source target : Fin k) (hst : source ≠ target)
    (before : Fin k → List Bool) :
    RunSpec (KS.W04.BinaryStackMoves.moveProgram source target) before
      (moveAfter source target before) ((before source).length+1) := by
  intro bits hbits
  exact KS.W04.BinaryStackMoves.run_move_stacks source target hst before bits hbits

def program {k : ℕ} (source target scratch : Fin k) : Program k :=
  compose (KS.W04.BinaryStackMoves.moveProgram source scratch)
    (KS.W04.BinaryStackMoves.moveProgram scratch target)

def after {k : ℕ} (source target : Fin k) (before : Fin k → List Bool) : Fin k → List Bool :=
  fun j => if j = source then [] else if j = target then before source ++ before target else before j

theorem spec {k : ℕ} (source target scratch : Fin k)
    (hst : source ≠ target) (hsc : source ≠ scratch) (hct : scratch ≠ target)
    (before : Fin k → List Bool) (hempty : before scratch = []) :
    RunSpec (program source target scratch) before (after source target before)
      (2 * (before source).length + 2) := by
  have h₁ := move_spec source scratch hsc before
  have h₂ := move_spec scratch target hct (moveAfter source scratch before)
  have h := h₁.compose h₂
  have he : moveAfter scratch target (moveAfter source scratch before) =
      after source target before := by
    funext j
    by_cases hjs : j = source
    · subst j
      simp [moveAfter, after, hst, hsc]
    · by_cases hjt : j = target
      · subst j
        simp [moveAfter, after, Ne.symm hst, Ne.symm hsc, Ne.symm hct, hempty]
      · by_cases hjc : j = scratch
        · subst j
          simp [moveAfter, after, hjs, hjt, hempty]
        · simp [moveAfter, after, hjs, hjt, hjc]
  have hf : (before source).length + 1 +
      ((moveAfter source scratch before) scratch).length + 1 =
      2 * (before source).length + 2 := by
    simp [moveAfter, Ne.symm hsc, hempty]
    omega
  simpa only [program, he, ← Nat.add_assoc, hf] using h

end KS.W07.WireAppend

end

end OAI
