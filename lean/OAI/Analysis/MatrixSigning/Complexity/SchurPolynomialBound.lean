import Mathlib
import OAI.Analysis.MatrixSigning.Machines.SchurTablePorts

namespace OAI

section

namespace KS.W07.SchurTableMachine

theorem inputLengthBudget_le_monomial (L : ℕ) :
    inputLengthBudget L ≤ KS.W29.polynomialFuel 2000000000000 5 L := by
  unfold inputLengthBudget totalTicks SchurLoopState.rowBudget SchurLoopState.columnBudget
    SchurCellMachine.cellBudget KS.W29.polynomialFuel
  ring_nf
  omega

theorem polynomial_input_spec {n : ℕ} (M : DenseRatMatrix (n+1)) :
    KS.W03.MachineCombinators.RunSpec program (inputState M) (outputState M)
      (KS.W29.polynomialFuel 2000000000000 5 (KS.W08.denseMatrixTape M).length) :=
  (input_length_spec M).mono (inputLengthBudget_le_monomial _)

theorem onPorts_polynomial_spec {k n : ℕ} (ports : Fin 32 ↪ Fin k)
    (spare : Fin k → List Bool) (M : DenseRatMatrix (n+1)) :
    KS.W03.MachineCombinators.RunSpec (KS.W29.FixedSequential.liftPorts program ports)
      (KS.W06.RationalCompare.replacePorts ports spare (inputState M))
      (KS.W06.RationalCompare.replacePorts ports spare (outputState M))
      (KS.W29.polynomialFuel 2000000000000 5 (KS.W08.denseMatrixTape M).length) :=
  (onPorts_input_length_spec ports spare M).mono (inputLengthBudget_le_monomial _)

end KS.W07.SchurTableMachine

end

end OAI
