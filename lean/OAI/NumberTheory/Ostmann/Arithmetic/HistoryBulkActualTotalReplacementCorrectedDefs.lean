import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalCorrected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentFibreReferenceDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkActualGoodPrincipal
open HistoryBulkIndependentFibreReference
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def correctedFinalAverage (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (hl : l<k) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (hV : SpectatorResidueBounds C spectator l) : ℂ :=
  if he : PreservesRemainingBands _ e then
    (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
      (fun ds=>correctedPrincipal C spectator ds hl e he (hV ds))
    else 0

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
