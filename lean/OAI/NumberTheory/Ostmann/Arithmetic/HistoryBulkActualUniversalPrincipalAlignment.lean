import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentBackground
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalSelectedReplacement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkSourceDisintegration
open HistoryBulkActualPrincipalBlockFamily HistoryBulkFibreGiantErrorAverage
open HistoryBulkUniversalPatternAggregation
attribute [local instance] Classical.propDecidable
local instance universalAlignmentReplacementInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (hout : ∀q∈spectatorList spectator ds,q∈spectator.candidates)
  (mixed : Bool)
  (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem replacementBackground_eq_plainPrincipal :
    HistoryBulkPatternIntegralReplacement.backgroundValue true
      (fun background pattern diagonal =>
        selectedReplacementBackground C (spectatorList spectator ds) hactual hl hout
          background pattern diagonal mixed)
      false mixed hV =
    HistoryBulkActualGoodPrincipal.plainPrincipal (l:=l) C spectator ds hactual hl
      (Equiv.refl (Fin (2^l) × Fin (2*(bulkSize k L/2)))) mixed hV :=
  (selectedAggregate_eq_replacementBackground (spectator:=spectator) (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C (spectatorList spectator ds)
    hactual hl hout mixed hV).symm.trans
      (selectedAggregate_eq_plainPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C spectator ds hactual hl hout mixed hV)

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
