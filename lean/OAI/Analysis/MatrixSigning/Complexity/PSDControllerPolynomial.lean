import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.NaturalPolynomial
import OAI.Analysis.MatrixSigning.Machines.ControllerRuntime

namespace OAI

section

namespace KS.W23.PSDControllerPolynomial
open KS.W07 KS.W17 KS.W17.FixedPSD KS.W03.MachineCombinators

def X : NaturalPolynomial := .variable
private def inverseP : NaturalPolynomial :=
  X*(X*X)+(X*X+(X*(X*X)+X)*X)+1
private def matrixP : NaturalPolynomial := X*X*(8*inverseP+15)
private def witnessHeightP : NaturalPolynomial := (X+1)*((X+2)*(3*inverseP+4))
private def witnessP : NaturalPolynomial := X*(8*witnessHeightP+15)
private def frameP : NaturalPolynomial := 4*X+2*matrixP+3
private def replayInputP : NaturalPolynomial := matrixP+X+witnessP
private def replayP : NaturalPolynomial :=
  10000000000000000000000000000*(replayInputP+1)^8+10*(replayInputP+1)+20
private def terminalP : NaturalPolynomial :=
  100000000*(matrixP+1)^4+1000000000000000000*(matrixP+1)^3+
    100*(matrixP+1)+matrixP+X+10+(X+1)*replayP
private def stepP : NaturalPolynomial :=
  NaturalPolynomial.constant PivotReachableBounds.stepCoefficient*(matrixP+1)^5

def controllerPolynomial : NaturalPolynomial :=
  (X+1)*(stepP+terminalP+X*frameP+1)

def coefficient : ℕ := controllerPolynomial.coefficient

theorem expression_eval (L : ℕ) : controllerPolynomial.eval L = originalControllerBound L L := rfl

theorem expression_degree : controllerPolynomial.degree = 58 := by decide

theorem originalControllerBound_mono_dim {N K : ℕ} (b : ℕ) (h : N ≤ K) :
    originalControllerBound N b ≤ originalControllerBound K b := by
  unfold originalControllerBound originalControllerStepBound originalTerminalBound
    originalFrameBound originalReplayStepBound originalReplayInputBound
    originalWitnessTapeBound originalMatrixTapeBound witnessHeightBudget
    KS.W30.inverseBitBound PivotReachableBounds.stepBudget
  gcongr

theorem originalControllerBound_le_monomial {N L : ℕ} (h : N ≤ L) :
    originalControllerBound N L ≤ coefficient*(L+1)^58 := by
  calc
    originalControllerBound N L ≤ originalControllerBound L L := originalControllerBound_mono_dim L h
    _ = controllerPolynomial.eval L := (expression_eval L).symm
    _ ≤ controllerPolynomial.coefficient*(L+1)^controllerPolynomial.degree :=
      controllerPolynomial.eval_le_input_polynomial L
    _ = coefficient*(L+1)^58 := by rw [expression_degree]; rfl

theorem controller_polynomial_spec {N : ℕ} (A : DenseRatMatrix N) :
    RunSpec controllerProgram (matrixState [] A)
      (witnessState (rationalNegativeWitness N (DenseRatMatrix.decode A)))
      (KS.W29.polynomialFuel coefficient 58 (KS.W08.denseMatrixTape A).length) :=
  (controller_payload_spec A).mono
    (originalControllerBound_le_monomial (KS.W19.TerminalWitnessMachine.dimension_le_payload A))

end KS.W23.PSDControllerPolynomial

end

end OAI
