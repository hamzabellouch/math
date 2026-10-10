import OAI.Combinatorics.ContingencyTables.Counting.CountingHistoryApplication
import OAI.Combinatorics.ContingencyTables.Counting.CountingConditionalAssembly

namespace OAI

/-! # The cell-bounded contingency-table FPRAS on one public fair-bit machine

The hypotheses are finite-box Prekopa-Leindler, finite-chain Cheeger
and Edmonds-Karp. They imply the guarantees for preprocessing, adaptive
phases, error amplification and fair-bit machine execution.
-/
namespace ContingencyTables.CountingExecutedMachine
open CompanionFactorialApplication GridBoundary

theorem counting_conditional
    (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I := Fin q) k)) :
    Algorithms.CountingStatement :=
  statement_of_single_law hEK hPL hCheeger
    (fun _ _ r c b hne epsilon delta he =>
      CountingPositiveProgram.value_source_sameLaw hEK r c b hne epsilon delta he)

end ContingencyTables.CountingExecutedMachine

end OAI
