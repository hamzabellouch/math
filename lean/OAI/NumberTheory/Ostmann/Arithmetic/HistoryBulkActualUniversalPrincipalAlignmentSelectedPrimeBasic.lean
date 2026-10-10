import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilyLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalSelectedProperties

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkSourceDisintegration
open HistoryBulkUniversalPatternAggregation HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualRootReferenceFamily HistoryBulkFibreGiantApproximation
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (hout : ∀q∈outside,q∈spectator.candidates)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources
    (Template.initial (2*(bulkSize k L/2)) k) l p)

theorem selectedFamily_eq_empty_of_none (mixed : Bool) (hD : outerData? C p o=none) :
    selectedFamily C outside hactual hl hout p o mixed = emptyFamily C outside p := by
  unfold selectedFamily
  rw [hD]

theorem selectedFamily_prime_eq_of_some (D : OuterData C p o)
    (hD : outerData? C p o=some D) :
    selectedFamily C outside hactual hl hout p o false =
      withDensity
        (primePatternFamily C outside (Equiv.refl _) (outerNonbulk C l p o)
          p D.blockDraw D.valid (fun _ _ _ _=>1)
          hactual hl D.nonbulk_pos D.left_mass D.right_mass
          (fun q hq=>⟨⟨q,hout q hq⟩,rfl⟩)) false := by
  unfold selectedFamily
  rw [hD]
  rfl

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
