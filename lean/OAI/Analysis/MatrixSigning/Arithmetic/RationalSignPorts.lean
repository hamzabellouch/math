import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalSignAction

namespace OAI

section

namespace KS.W16.RationalSignAction
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare (replacePorts replacePorts_on replacePorts_off)

def portInput {k : ℕ} (ports : Fin 14 ↪ Fin k) (spare : Fin k → List Bool)
    (wire tape : List Bool) : Fin k → List Bool := replacePorts ports spare (inputState wire tape)
def portOutput {k : ℕ} (ports : Fin 14 ↪ Fin k) (spare : Fin k → List Bool)
    (wire tape : List Bool) : Fin k → List Bool := replacePorts ports spare (outputState wire tape)

theorem onPorts_spec {k : ℕ} (ports : Fin 14 ↪ Fin k) (spare : Fin k → List Bool)
    (q : ℚ) (eps : Bool) (tail : List Bool) :
    RunSpec (KS.W29.FixedSequential.liftPorts program ports)
      (portInput ports spare (KS.W01.encodeRat q) (eps :: tail))
      (portOutput ports spare (KS.W01.encodeRat (signedRational eps q)) (eps :: tail))
      (64 * (KS.W01.ratLength q + 1)) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec program ports _ _ _ _ _ (linear_spec q eps tail)
  · intro i; exact replacePorts_on ports spare _ i
  · intro i; exact replacePorts_on ports spare _ i
  · intro j hj
    exact (replacePorts_off ports spare _ j hj).trans (replacePorts_off ports spare _ j hj).symm

theorem negation_onPorts_spec {k : ℕ} (ports : Fin 14 ↪ Fin k) (spare : Fin k → List Bool)
    (q : ℚ) (tail : List Bool) :
    RunSpec (KS.W29.FixedSequential.liftPorts program ports)
      (portInput ports spare (KS.W01.encodeRat q) (false :: tail))
      (portOutput ports spare (KS.W01.encodeRat (-q)) (false :: tail))
      (64 * (KS.W01.ratLength q + 1)) := onPorts_spec ports spare q false tail

end KS.W16.RationalSignAction

end

end OAI
