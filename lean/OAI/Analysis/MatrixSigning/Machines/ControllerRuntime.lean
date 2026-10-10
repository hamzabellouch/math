import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.PivotControllerCorrectness
import OAI.Analysis.MatrixSigning.Machines.ControllerTerminalBound
import OAI.Analysis.MatrixSigning.Matrices.PivotReachableBounds

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def originalControllerStepBound (N b : ℕ) : ℕ :=
  KS.W23.PivotReachableBounds.stepBudget (originalMatrixTapeBound N b)+
    originalTerminalBound N b+N*originalFrameBound N b+1

def originalControllerBound (N b : ℕ) : ℕ := (N+1)*originalControllerStepBound N b

theorem ControllerReachable.controller_ticks_le {N n : ℕ} {A : DenseRatMatrix N}
    {M : DenseRatMatrix n} {h : PivotHistory n N} (hr : ControllerReachable A M h) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b) :
    controllerTicks h M ≤ (n+1)*originalControllerStepBound N b := by
  induction n with
  | zero =>
    have hh := hr.history_tape_length b hnum hden
    have hd := h.dimension_depth
    simp only [zero_add] at hd
    simp only [controllerTicks,zero_add,one_mul]
    rw [hd] at hh
    unfold originalControllerStepBound
    omega
  | succ n ih =>
    by_cases ht : pivotTerminal (DenseRatMatrix.decode M) = none
    · have hs := KS.W23.PivotReachableBounds.reachable_step_bound hr b hnum hden
      have hc := ih (M:=child M) (h:=PivotHistory.push (DenseRatMatrix.decode M) h)
        (ControllerReachable.descend hr ht)
      have hsg : KS.W23.PivotReachableBounds.stepBudget (originalMatrixTapeBound N b) ≤
          originalControllerStepBound N b := by unfold originalControllerStepBound; omega
      rw [controllerTicks_descend h M ht]
      unfold KS.W23.PivotReachableBounds.stepTicks at hs
      nlinarith
    · have hb := hr.terminal_ticks_le b hnum hden ht
      have hbg : originalTerminalBound N b ≤ originalControllerStepBound N b := by
        unfold originalControllerStepBound
        omega
      nlinarith

theorem controller_original_spec {N : ℕ} (A : DenseRatMatrix N) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b) :
    RunSpec controllerProgram (matrixState [] A)
      (witnessState (rationalNegativeWitness N (DenseRatMatrix.decode A))) (originalControllerBound N b) :=
  (controller_spec N A).mono (ControllerReachable.controller_ticks_le ControllerReachable.initial b hnum hden)

theorem controller_payload_spec {N : ℕ} (A : DenseRatMatrix N) :
    RunSpec controllerProgram (matrixState [] A)
      (witnessState (rationalNegativeWitness N (DenseRatMatrix.decode A)))
      (originalControllerBound N (localBits A)) :=
  controller_original_spec A (localBits A)
    (fun i j => (KS.W19.TerminalWitnessMachine.entry_parts_le_payload A i j).1)
    (fun i j => (KS.W19.TerminalWitnessMachine.entry_parts_le_payload A i j).2)

end KS.W17.FixedPSD

end

end OAI
