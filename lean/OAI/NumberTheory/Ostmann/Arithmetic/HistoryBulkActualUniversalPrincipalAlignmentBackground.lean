import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalPlain
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentValue
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalDefs

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
local instance universalAlignmentBackgroundInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (hout : ∀q∈spectatorList spectator ds,q∈spectator.candidates)
  (mixed : Bool)
  (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem selectedAggregate_eq_plainPrincipal :
    selectedAggregate (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C (spectatorList spectator ds) hactual hl hout mixed hV =
      HistoryBulkActualGoodPrincipal.plainPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C spectator ds hactual hl
        (Equiv.refl (Fin (2^l) × Fin (2*(bulkSize k L/2)))) mixed hV :=
  (selectedAggregate_eq_background (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz)
    (L:=L) (k:=k) (l:=l) (E:=E) C (spectatorList spectator ds) hactual hl hout mixed hV).trans
    (congrArg ((backgroundPrior C l).cmean) (funext fun bg =>
      congrArg (patternComplexSum
        (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
          Internal (Template.initial (2*(bulkSize k L/2)) k) l) C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
        (funext fun p => funext fun b =>
          selectedFamily_value_eq_plainPattern_raw (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz)
            (L:=L) (k:=k) (l:=l) (E:=E) C spectator ds hactual hl hout p
            (restoreOuterBackground C l p bg b) mixed b hV)))

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
