import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.ReusableArrayLookup
import OAI.Analysis.MatrixSigning.Arithmetic.CleanRationalCompare
import OAI.Analysis.MatrixSigning.Machines.BinaryStackDeterministic

namespace OAI

namespace KS.W04
open KS.W29.Deterministic KS.W29.FixedSequential

namespace ReusableArrayLookup

theorem reoutput_coinIndependent {k : Nat} (P : Program k) (output : Fin k)
    (hP : CoinIndependent P) : CoinIndependent (reoutput P output) := by
  intro c a b
  exact (step_reoutput P output c a).trans
    ((hP c a b).trans (step_reoutput P output c b).symm)

end ReusableArrayLookup
namespace CleanRationalCompare

theorem halt_coinIndependent {k : Nat} (output : Fin k) :
    CoinIndependent (haltProgram output) :=
  coinIndependent_compile (0 : Fin 1) output output _ (by intros; rfl)

theorem clearList_coinIndependent {k : Nat} (output : Fin k) (ports : List (Fin k)) :
    CoinIndependent (clearListProgram output ports) := by
  induction ports with
  | nil => exact halt_coinIndependent output
  | cons p ps ih => exact coinIndependent_compose _ _ (BinaryStackMoves.clear_coinIndependent p) ih

theorem cleanup_coinIndependent : CoinIndependent cleanupProgram :=
  clearList_coinIndependent 9 scratchPorts

end CleanRationalCompare
end KS.W04

end OAI
