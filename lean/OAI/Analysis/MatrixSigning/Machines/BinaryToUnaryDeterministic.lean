import Mathlib
import OAI.Analysis.MatrixSigning.Machines.BinaryToUnaryMachine
import OAI.Analysis.MatrixSigning.Machines.MachineRoundTrip

namespace OAI

section

namespace KS.W03.BinaryToUnary
open KS.W29.FixedSequential KS.W29.Deterministic

def program : Program 3 := ofMachine machine

theorem coinIndependent : CoinIndependent program :=
  coinIndependent_compile (0 : Fin 8) (0 : Fin 3) (1 : Fin 3) dispatch
    (fun _ _ _ _ => rfl)

theorem run_eq_of_same_length (c : KS.W01.FixedStack.Config 3 8)
    (xs ys : List Bool) (hlen : xs.length = ys.length) :
    machine.run c xs = machine.run c ys :=
  KS.W03.MachineRoundTrip.deterministic_run machine coinIndependent c xs ys hlen

end KS.W03.BinaryToUnary

end

end OAI
