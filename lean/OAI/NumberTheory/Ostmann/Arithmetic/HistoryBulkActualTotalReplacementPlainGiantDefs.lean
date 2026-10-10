import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementOriginalDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSelectedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSourceMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFixedReferenceTermSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantErrorAverage
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def plainGiantAverage (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
    (hl : l ≤ k) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) (mixed : Bool) : ℂ :=
  if mixed then originalSourceAverage C spectator (mixedSelectedPrincipal C spectator hactual hl σ)
  else originalSourceAverage C spectator (primeSelectedPrincipal C spectator hactual hl σ)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
