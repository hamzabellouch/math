import Mathlib
import OAI.Analysis.MatrixSigning.Machines.MachineRoundTrip
import OAI.Analysis.MatrixSigning.Machines.FixedCopyRestore

namespace OAI

section

namespace KS.W07
open KS.W29.FixedSequential KS.W03.MachineCombinators

theorem fixedCopy_spec {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (before : Fin k → List Bool) (xs : List Bool)
    (hsrc : before (ports 0) = xs) (hdst : before (ports 1) = [])
    (hscratch : before (ports 2) = []) :
    RunSpec (KS.W01.FixedCopy.program ports) before
      (Function.update before (ports 1) xs) (2 * xs.length + 2) := by
  unfold KS.W01.FixedCopy.program
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hlen
  exact KS.W01.FixedCopy.run_copy_restore ports before xs bits hsrc hdst hscratch hlen

end KS.W07

end

end OAI
