import Mathlib
import OAI.Analysis.MatrixSigning.Machines.MachineCombinators
import OAI.Analysis.MatrixSigning.Machines.BinaryStackMoves

namespace OAI

section

namespace KS.W15.RationalMultiply
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def clearAfter {k : Nat} (port : Fin k) (before : Fin k → List Bool) : Fin k → List Bool :=
  fun j => if j = port then [] else before j

theorem clear_spec {k : Nat} (port : Fin k) (before : Fin k → List Bool) :
    RunSpec (KS.W04.BinaryStackMoves.clearProgram port) before
      (clearAfter port before) ((before port).length + 1) := by
  intro bits hlen
  exact KS.W04.BinaryStackMoves.run_clear_stacks port before bits hlen

def moveAfter {k : Nat} (source target : Fin k) (before : Fin k → List Bool) :
    Fin k → List Bool :=
  fun j => if j = source then [] else if j = target then (before source).reverse ++ before target
    else before j

theorem move_spec {k : Nat} (source target : Fin k) (hst : source ≠ target)
    (before : Fin k → List Bool) :
    RunSpec (KS.W04.BinaryStackMoves.moveProgram source target) before
      (moveAfter source target before) ((before source).length + 1) := by
  intro bits hlen
  exact KS.W04.BinaryStackMoves.run_move_stacks source target hst before bits hlen

end KS.W15.RationalMultiply

end

end OAI
