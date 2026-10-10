import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalSubtractCorrect

namespace OAI

section

namespace KS.W13.RationalSubtract
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare (replacePorts replacePorts_on replacePorts_off)

def portInput {k : ℕ} (ports : Fin 19 ↪ Fin k) (spare : Fin k → List Bool)
    (wire : List Bool) : Fin k → List Bool := replacePorts ports spare (inputState wire)
def portOutput {k : ℕ} (ports : Fin 19 ↪ Fin k) (spare : Fin k → List Bool)
    (wire : List Bool) : Fin k → List Bool := replacePorts ports spare (outputState wire)

theorem onPorts_spec {k : ℕ} (ports : Fin 19 ↪ Fin k) (spare : Fin k → List Bool) (q r : ℚ) :
    RunSpec (KS.W29.FixedSequential.liftPorts program ports)
      (portInput ports spare (KS.W01.encodeRat q ++ KS.W01.encodeRat r))
      (portOutput ports spare (KS.W01.encodeRat (q-r)))
      (KS.W29.polynomialFuel 600000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec program ports _ _ _ _ _ (polynomial_spec q r)
  · intro i; exact replacePorts_on ports spare _ i
  · intro i; exact replacePorts_on ports spare _ i
  · intro j hj
    exact (replacePorts_off ports spare (outputState (KS.W01.encodeRat (q-r))) j hj).trans
      (replacePorts_off ports spare (inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat r)) j hj).symm

theorem onPorts_preserves {k : ℕ} (ports : Fin 19 ↪ Fin k) (spare : Fin k → List Bool)
    (q r : ℚ) (bits : List Bool)
    (hlen : KS.W29.polynomialFuel 600000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length ≤ bits.length)
    (j : Fin k) (hj : ∀ i,j ≠ ports i) :
    (((KS.W29.FixedSequential.liftPorts program ports).toMachine.run
      ⟨some (KS.W29.FixedSequential.liftPorts program ports).initial,
        portInput ports spare (KS.W01.encodeRat q ++ KS.W01.encodeRat r)⟩ bits).«stacks» j) = spare j := by
  have h := congrArg (fun c => c.«stacks» j) ((onPorts_spec ports spare q r).run_of_le bits hlen)
  exact h.trans (replacePorts_off ports spare _ j hj)

end KS.W13.RationalSubtract

end

end OAI
