import Mathlib
import OAI.Analysis.MatrixSigning.Machines.BinaryStackMoves
import OAI.Analysis.MatrixSigning.Machines.Deterministic

namespace OAI

section

namespace KS.W04.BinaryStackMoves
open KS.W29.Deterministic

theorem clear_coinIndependent {k : Nat} (port : Fin k) :
    CoinIndependent (clearProgram port) :=
  coinIndependent_compile (0 : Fin 1) port port (clearDispatch port) (by intros; rfl)

theorem move_coinIndependent {k : Nat} (source target : Fin k) :
    CoinIndependent (moveProgram source target) :=
  coinIndependent_compile (0 : Fin 1) source target (moveDispatch source target) (by intros; rfl)

end KS.W04.BinaryStackMoves

end

end OAI
