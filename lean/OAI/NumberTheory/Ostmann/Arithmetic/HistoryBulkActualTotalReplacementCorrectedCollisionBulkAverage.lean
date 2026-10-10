import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualIntegralReplacementCorrectedDefsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedBulkDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference HistoryBulkActualIntegralReplacement
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem correctedBulkAverage_eq_guarded
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (hl : l<k) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (hV : SpectatorResidueBounds C spectator l) :
    correctedBulkAverage (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
      C spectator hl e hV =
      if he : PreservesRemainingBands _ e then
        (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
          (fun ds => correctedBulkPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
            (k:=k) (l:=l) (E:=E) C spectator ds hl e he (hV ds))
      else 0 := by
  by_cases he : PreservesRemainingBands _ e
  · simp only [correctedBulkAverage, dite_eq_left he]
  · simp only [correctedBulkAverage, dite_eq_right he]

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
