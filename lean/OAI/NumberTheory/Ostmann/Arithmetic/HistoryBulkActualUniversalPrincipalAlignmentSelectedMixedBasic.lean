import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilyLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalSelectedProperties
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationFibreIdentities
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSelectedDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkSourceDisintegration
open HistoryBulkUniversalPatternAggregation HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualRootReferenceFamily HistoryBulkFibreGiantApproximation
open HistoryGiantReferenceMean HistoryBulkFibreOriginalReference
open HistoryBulkFibreGiantApproximationReference HistoryBulkFibreGiantErrorAverage
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k)
  (hout : ∀q∈spectatorList spectator ds,q∈spectator.candidates)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources
    (Template.initial (2*(bulkSize k L/2)) k) l p)
  (b : Block p → CommonSample C.sources
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
  (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem selectedFamily_mixed_eq_of_some (D : OuterData C p o)
    (hD : outerData? C p o=some D) :
    selectedFamily C (spectatorList spectator ds) hactual hl hout p o true =
      withDensity (mixedPatternFamily C (spectatorList spectator ds) (Equiv.refl _)
        (outerNonbulk C l p o) p D.blockDraw D.valid
        (fun i=>plainMixedWeight C (spectatorList spectator ds) (outerNonbulk C l p o) i.1.val)
        hactual hl D.nonbulk_pos D.left_mass D.right_mass
        (spectatorList_source spectator ds)) true := by
  simp only [selectedFamily,hD,ite_true]

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
