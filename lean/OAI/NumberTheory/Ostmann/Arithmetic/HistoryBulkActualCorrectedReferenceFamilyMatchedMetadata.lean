import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedReferenceFamilyMatchedReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceSourceBoundsBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualCorrectedReferenceFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryCompensationRepresentativePatterns
open HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference
open HistoryBulkIndependentFibreReference HistoryGiantOriginalMeanFactorization HistorySignedXiTransport
open HistoryPairPattern HistoryGiantReferenceMean HistoryBulkFibreGiantApproximationReference
open HistoryPairBulkTransport HistoryGiantReferenceSourceBounds
open HistoryDiagonalRemainingRootMatching HistoryBulkIndependentReferenceFrequency
attribute [local instance] Classical.propDecidable
local instance correctedMatchedMetadataInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : BlockDraw p (CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)))
  (hb : ∀ i, (expand p b i).val ∈ (C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l i)).candidates)
  (outside : List ℕ) (a : SelectedNonbulkSample C l)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) (s t : ℤ)
  (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l)
  (r : Witness C outside a e s t
    (blockLeftChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l p b hb f)
    (blockRightChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l p b hb g))

theorem matchedWitnessBlockReference_rootAligned (he : PreservesRemainingBands _ e)
    (j : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length) :
    coordinateSample _ (matchedWitnessBlockReference C p b hb outside a e s t f g r he).right.history
      (matchedWitnessBlockReference C p b hb outside a e s t f g r he).right.labels (.inr (.inl j)) =
    coordinateSample _ (matchedWitnessBlockReference C p b hb outside a e s t f g r he).left.history
      (matchedWitnessBlockReference C p b hb outside a e s t f g r he).left.labels
        (.inr (.inl (fullPermutation (l+1) _ e he j))) := by
  have hleft := coordinateSample_root_assigned C.sources _ (frequencyBound Bs BD Bz k L) l
    (matchedWitnessLeftRoot C p b hb outside a e s t f g r)
    (blockLeftChoices C.sources _ (frequencyBound Bs BD Bz k L) l p b hb f)
    (fibreAssignment C a r.bulk) rfl (Template.assignedSlots_matches _ _ _)
    (fullPermutation (l+1) _ e he j)
  have hright := coordinateSample_root_assigned C.sources _ (frequencyBound Bs BD Bz k L) l
    (matchedWitnessRightRoot C p b hb outside a e s t f g r)
    (blockRightChoices C.sources _ (frequencyBound Bs BD Bz k L) l p b hb g)
    (rightAssignment C a e r.bulk r.compatible) rfl (Template.assignedSlots_matches _ _ _) j
  have hvalues := counterpartCurrentAssignment_value C (fibreAssignment C a r.bulk) e he r.compatible j
  exact hright.trans ((congrArg (fun v : ℕ => (v : ℤ)) hvalues).trans hleft.symm)

def matchedWitnessPrincipalData (he : PreservesRemainingBands _ e)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l
      (blockLeftChoices C.sources _ (frequencyBound Bs BD Bz k L) l p b hb f) ≠ 0)
    (hechoices : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l
      (blockRightChoices C.sources _ (frequencyBound Bs BD Bz k L) l p b hb g) ≠ 0)
    (n : ℕ) (hlen : outside.length = 2*n) (hprime : ∀q ∈ outside, q.Prime)
    (hV : ∀q ∈ outside, ∀j ≤ l, frequencyBound Bs BD Bz k L j < q)
    (independent : Bool) : MatchedPrincipalReferenceData C
      (matchedWitnessBlockReference C p b hb outside a e s t f g r he) := by
  have href := corrected_reference_data C outside a e s t
    (blockLeftChoices C.sources _ (frequencyBound Bs BD Bz k L) l p b hb f)
    (blockRightChoices C.sources _ (frequencyBound Bs BD Bz k L) l p b hb g) r ha
  have hs := selected_reference_sourceBounds C (frequencyBound Bs BD Bz k L) l
    (fibreAssignment C a r.bulk) (rightAssignment C a e r.bulk r.compatible) s t
    (blockLeftChoices C.sources _ (frequencyBound Bs BD Bz k L) l p b hb f)
    (blockRightChoices C.sources _ (frequencyBound Bs BD Bz k L) l p b hb g)
    (mixedP C.giantCenter C.giant r.draw) (mixedQ C.giantCenter C.giant r.draw)
    href.left_mass href.right_mass hc hechoices href.plus_pos href.minus_pos href.plus_cell href.minus_cell
  exact {
    leftSource := hs.1
    rightSource := hs.2
    s := n
    outsideLength := hlen
    outsidePrime := hprime
    outsideFrequency := hV
    permutation := inducedBulkPermutation (2*(bulkSize k L/2)) k l
      (fullPermutation (l+1) _ e he) (fullPermutation_bulk (l+1) _ e he)
    K := k
    independent := independent }

end Ostmann.Arithmetic.HistoryBulkActualCorrectedReferenceFamily

end

end OAI
