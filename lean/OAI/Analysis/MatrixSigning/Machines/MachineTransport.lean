import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedSequential

namespace OAI

section

namespace KS.W19.MachineTransport
open KS.W01.FixedStack KS.W29.FixedSequential

theorem run_ofMachine (M : Machine) (c : Config M.stackCount M.states) (bits : List Bool) :
    (ofMachine M).toMachine.run c bits=M.run c bits := by
  cases M
  rfl

end KS.W19.MachineTransport

end

end OAI
