import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalCorrectedFamily
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedFalseBlock
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSelectedBlockDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSelectedMeanDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSelectedPattern
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionFalseAlgebra
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionNormalForm
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindexPatterns

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkPrincipalCollisionError HistoryBulkActualGoodPrincipal
open HistoryBulkActualPrincipalCollision HistoryBulkIndependentFibreReference
open HistoryBulkUniversalPatternAggregation HistoryBulkPrincipalSourceReindex
open HistoryBulkFibreIntegralReplacementFrame HistoryBulkFibreOriginalReference
attribute [local instance] Classical.propDecidable actualGoodCorrectedFamilyInternalDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands _ e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (bg : Background C l)

theorem selectedCollisionMean_false_eq_pattern (corrected mixed : Bool) :
    selectedCollisionMean (l:=l) C outside e he hlen hp hV bg
      corrected mixed false =
    patternComplexSum C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
      (fun p b=>HistoryBulkPatternIntegralReplacement.familyValue (C:=C) (outside:=outside) (l:=l) (p:=p) false
        (correctedFamily (l:=l) C p (restoreOuterBackground C l p bg b) outside e he hp) b corrected mixed hV) :=
  @Eq.trans ℂ _ _ _
    (@selectedCollisionMean_eq_pattern d Bs BD Bz L k l E C outside e he hlen hp hV bg corrected mixed false)
    (patternComplexSum_congr_pointwise
      (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕ Internal (Template.initial (2*(bulkSize k L/2)) k) l)
      C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l) _ _
      (fun p b=>@selectedCollisionBlockValue_false_eq_family d Bs BD Bz L k l E C outside e he hlen hp hV bg corrected mixed p b))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

end

end OAI
