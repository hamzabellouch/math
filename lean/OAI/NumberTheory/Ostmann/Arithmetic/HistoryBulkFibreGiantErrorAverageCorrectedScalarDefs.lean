import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageCorrectedSelectedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSourceMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentFibreReferenceDefs
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalEnvironment

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference
attribute [local instance] Classical.propDecidable

def correctedGuardedPrincipalAverage {d : Decomposition} {Bs BD Bz L : ℝ}
    {k l : ℕ} {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) : ℂ :=
  if he : PreservesRemainingBands _ e then
    originalSourceAverage C spectator (correctedSelectedPrincipal C spectator e he)
  else 0

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
