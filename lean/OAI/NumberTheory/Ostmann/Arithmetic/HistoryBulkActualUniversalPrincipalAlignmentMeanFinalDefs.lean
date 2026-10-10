import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalPlain
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion HistoryBulkSourceDisintegration
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem plainFinalAverage_eq_cmean
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
    (hl : l ≤ k) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (mixed : Bool)
    (hV : HistoryBulkActualTotalReplacement.SpectatorResidueBounds C spectator l) :
    HistoryBulkActualTotalReplacement.plainFinalAverage
      (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
      C spectator hactual hl σ mixed hV =
    (spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds =>
      HistoryBulkActualGoodPrincipal.plainPrincipal
        (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
        C spectator ds hactual hl σ mixed (hV ds)) := by
  unfold HistoryBulkActualTotalReplacement.plainFinalAverage
  rfl

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
