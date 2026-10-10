import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSourceMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceDisintegration

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantErrorAverage
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def plainOriginalAverage (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2)))) (mixed : Bool) : ℂ :=
  if mixed then originalSourceAverage C spectator (mixedOriginalValue C spectator σ)
  else originalSourceAverage C spectator (primeOriginalValue C spectator σ)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
