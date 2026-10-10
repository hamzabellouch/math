import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedReferenceFamilyBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagPrincipalMatchedData

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
attribute [local instance] Classical.propDecidable
local instance correctedMatchedReferenceInternalDecidable (seed : List SourceSlot) (l : ℕ) :
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

def matchedWitnessLeftRoot : State :=
  giantState (sourceState C.sources _ (fibreAssignment C a r.bulk) s)
    (mixedP C.giantCenter C.giant r.draw) (mixedQ C.giantCenter C.giant r.draw)

def matchedWitnessRightRoot : State :=
  giantState (sourceState C.sources _ (rightAssignment C a e r.bulk r.compatible) t)
    (mixedP C.giantCenter C.giant r.draw) (mixedQ C.giantCenter C.giant r.draw)

def matchedWitnessBlockReference (he : PreservesRemainingBands _ e) :
    MatchedBlockReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) outside l p where
  blockDraw := b
  valid := hb
  leftRoot := matchedWitnessLeftRoot C p b hb outside a e s t f g r
  rightRoot := matchedWitnessRightRoot C p b hb outside a e s t f g r
  leftFrequency := f
  rightFrequency := g
  leftMatch := Template.assignedSlots_matches C.sources _ (fibreAssignment C a r.bulk)
  rightMatch := Template.assignedSlots_matches C.sources _ (rightAssignment C a e r.bulk r.compatible)
  leftSupported := r.supported.1
  rightSupported := r.supported.2
  rootMatching := corrected_reference_draw_matching C outside a e s t _ _ r he

@[simp] theorem matchedWitnessBlockReference_left_frequency (he : PreservesRemainingBands _ e) :
    (matchedWitnessBlockReference C p b hb outside a e s t f g r he).leftRoot.frequency = s := rfl

@[simp] theorem matchedWitnessBlockReference_right_frequency (he : PreservesRemainingBands _ e) :
    (matchedWitnessBlockReference C p b hb outside a e s t f g r he).rightRoot.frequency = t := rfl

theorem matchedWitnessBlockReference_giants (he : PreservesRemainingBands _ e) :
    RootGiantsAgree (matchedWitnessBlockReference C p b hb outside a e s t f g r he).left.history
      (matchedWitnessBlockReference C p b hb outside a e s t f g r he).right.history := by
  constructor <;> simp only [MatchedBlockReference.left_root,MatchedBlockReference.right_root] <;> rfl

end Ostmann.Arithmetic.HistoryBulkActualCorrectedReferenceFamily

end

end OAI
