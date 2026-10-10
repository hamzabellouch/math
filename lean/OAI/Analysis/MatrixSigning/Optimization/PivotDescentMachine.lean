import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.PivotHistoryMachine
import OAI.Analysis.MatrixSigning.Machines.SchurTableCorrectness

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def schurPorts : Fin 32 ↪ Fin 35 := Fin.castLEEmb (by decide)
def schurProgram : Program 35 := liftPorts KS.W07.SchurTableMachine.program schurPorts

def matrixState {n : ℕ} (saved : List Bool) (M : DenseRatMatrix n) : Fin 35 → List Bool :=
  state saved (Computability.encodeNat n) (KS.W08.denseMatrixTape M) [] []

def child {n : ℕ} (M : DenseRatMatrix (n+1)) : DenseRatMatrix n :=
  DenseRatMatrix.ofMatrix (schurTail (DenseRatMatrix.decode M))

theorem schur_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) :
    RunSpec schurProgram (matrixState saved M)
      (state saved (Computability.encodeNat (n+1)) (KS.W08.denseMatrixTape M)
        (Computability.encodeNat n) (KS.W08.denseMatrixTape (child M)))
      (KS.W07.SchurTableMachine.totalTicks n b) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec KS.W07.SchurTableMachine.program schurPorts
    (KS.W07.SchurTableMachine.inputState M) (KS.W07.SchurTableMachine.outputState M) _ _ _
    (KS.W07.SchurTableMachine.full_spec M b hnum hden)
  · intro i; fin_cases i <;> simp [matrixState,state,schurPorts,KS.W07.SchurTableMachine.inputState]
  · intro i; fin_cases i <;> simp [state,schurPorts,child,KS.W07.SchurTableMachine.outputState]
  · intro j hj
    have h23 : j ≠ 23 := by simpa [schurPorts] using hj 23
    have h30 : j ≠ 30 := by simpa [schurPorts] using hj 30
    simp [matrixState,state,h23,h30]

def fullDescendProgram : Program 35 := compose schurProgram descendProgram

def descentTicks {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ) : ℕ :=
  KS.W07.SchurTableMachine.totalTicks n b +
    (24*(Computability.encodeNat (n+1)).length+8*(KS.W08.denseMatrixTape M).length+
      2*(Computability.encodeNat n).length+2*(KS.W08.denseMatrixTape (child M)).length+26)

theorem fullDescend_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) :
    RunSpec fullDescendProgram (matrixState saved M)
      (matrixState (savedFrame (Computability.encodeNat (n+1)) (KS.W08.denseMatrixTape M) ++ saved) (child M))
      (descentTicks M b) :=
  (schur_spec saved M b hnum hden).compose
    (descend_spec saved (Computability.encodeNat (n+1)) (KS.W08.denseMatrixTape M)
      (Computability.encodeNat n) (KS.W08.denseMatrixTape (child M)))

end KS.W17.FixedPSD

end

end OAI
