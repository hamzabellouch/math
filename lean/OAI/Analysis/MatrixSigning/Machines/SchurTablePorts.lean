import Mathlib
import OAI.Analysis.MatrixSigning.Machines.SchurInputLength

namespace OAI

section

namespace KS.W07.SchurTableMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare (replacePorts replacePorts_on replacePorts_off)

theorem onPorts_spec {k n : ℕ} (ports : Fin 32 ↪ Fin k) (spare : Fin k → List Bool)
    (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B) :
    RunSpec (liftPorts program ports)
      (replacePorts ports spare (inputState M))
      (replacePorts ports spare (outputState M)) (totalTicks n B) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec program ports _ _ _ _ _ (full_spec M B hnum hden)
  · intro j; exact replacePorts_on ports spare _ j
  · intro j; exact replacePorts_on ports spare _ j
  · intro j hj
    exact (replacePorts_off ports spare (outputState M) j hj).trans
      (replacePorts_off ports spare (inputState M) j hj).symm

theorem onPorts_input_length_spec {k n : ℕ} (ports : Fin 32 ↪ Fin k)
    (spare : Fin k → List Bool) (M : DenseRatMatrix (n+1)) :
    RunSpec (liftPorts program ports)
      (replacePorts ports spare (inputState M))
      (replacePorts ports spare (outputState M))
      (inputLengthBudget (KS.W08.denseMatrixTape M).length) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec program ports _ _ _ _ _ (input_length_spec M)
  · intro j; exact replacePorts_on ports spare _ j
  · intro j; exact replacePorts_on ports spare _ j
  · intro j hj
    exact (replacePorts_off ports spare (outputState M) j hj).trans
      (replacePorts_off ports spare (inputState M) j hj).symm

end KS.W07.SchurTableMachine

end

end OAI
