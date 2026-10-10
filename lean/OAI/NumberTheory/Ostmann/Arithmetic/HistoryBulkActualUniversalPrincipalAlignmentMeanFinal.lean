import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentMeanFinalDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalSelectedReplacement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion HistoryBulkSourceDisintegration
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l ≤ k)
  (hout : ∀ ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,
    ∀ q ∈ spectatorList spectator ds, q ∈ spectator.candidates)
  (mixed : Bool)
  (hV : ∀ ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,
    ∀ q ∈ spectatorList spectator ds, ∀ j ≤ l, frequencyBound Bs BD Bz k L j < q)

theorem replacementMean_eq_plainFinalAverage :
    (spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds =>
      HistoryBulkPatternIntegralReplacement.backgroundValue true
        (fun background pattern diagonal =>
          selectedReplacementBackground C (spectatorList spectator ds) hactual hl (hout ds)
            background pattern diagonal mixed)
        false mixed (hV ds)) =
      HistoryBulkActualTotalReplacement.plainFinalAverage (l:=l) C spectator hactual hl
        (Equiv.refl (Fin (2^l) × Fin (2*(bulkSize k L/2)))) mixed hV :=
  (replacementMean_eq_plainPrincipalMean
    (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
    C spectator hactual hl hout mixed hV).trans
      (plainFinalAverage_eq_cmean
        (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
        C spectator hactual hl
        (Equiv.refl (Fin (2^l) × Fin (2*(bulkSize k L/2)))) mixed hV).symm

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
