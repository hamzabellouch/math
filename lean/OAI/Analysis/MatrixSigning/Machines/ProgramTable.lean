import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedSequential

namespace OAI

section

namespace KS.W07
open KS.W29.FixedSequential

theorem compose_table_length {k : ℕ} (P Q : Program k) :
    (compose P Q).table.length = (compose P Q).states * (3^k*2) := by
  change (KS.W01.FixedStack.compile (leftState P Q P.initial) P.input Q.output
    (dispatch P Q)).table.length = (P.states + Q.states) * (3^k*2)
  exact KS.W01.FixedStack.compile_table_length _ _ _ _

end KS.W07

end

end OAI
