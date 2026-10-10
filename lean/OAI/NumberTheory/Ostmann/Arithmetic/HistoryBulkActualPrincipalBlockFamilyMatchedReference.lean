import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReferencePlain
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagPrincipalMatchedData

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryCompensationRepresentativePatterns
open HistoryBulkActualRootReferenceFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreOriginalReference HistoryGiantOriginalMeanFactorization HistorySignedXiTransport
open HistoryPairPattern HistoryGiantReferenceMean HistoryBulkFibreGiantApproximationReference
attribute [local instance] Classical.propDecidable
local instance actualPrincipalMatchedReferenceInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : BlockDraw p (CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)))
  (hb : ∀ i, (expand p b i).val ∈ (C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l i)).candidates)
  (outside : List ℕ)
  (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (a : SelectedNonbulkSample C l)
  (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α → ℝ) (P Q : α → ℤ)
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
  (r : Witness C outside σ a (leftBlockDraws C p b hb) (rightBlockDraws C p b hb) J w P Q i)

def matchedWitnessLeftRoot : State :=
  giantState (sourceState C.sources _ (fibreAssignment C a r.bulk) i.1.val) (P r.giant) (Q r.giant)

def matchedWitnessRightRoot : State :=
  giantState (sourceState C.sources _ (permuteAssignment C σ (fibreAssignment C a r.bulk)) i.1.val)
    (P r.giant) (Q r.giant)

def matchedWitnessBlockReference :
    MatchedBlockReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) outside l p where
  blockDraw := b
  valid := hb
  leftRoot := matchedWitnessLeftRoot C p b hb outside σ a J w P Q i r
  rightRoot := matchedWitnessRightRoot C p b hb outside σ a J w P Q i r
  leftFrequency := i.2.1
  rightFrequency := i.2.2
  leftMatch := Template.assignedSlots_matches C.sources _ (fibreAssignment C a r.bulk)
  rightMatch := Template.assignedSlots_matches C.sources _ (permuteAssignment C σ (fibreAssignment C a r.bulk))
  leftSupported := r.supported.1
  rightSupported := r.supported.2
  rootMatching := plain_reference_matching C σ a i.1.val i.1.val
    (leftChoices C (leftBlockDraws C p b hb) i)
    (rightChoices C (rightBlockDraws C p b hb) i) r.bulk (P r.giant) (Q r.giant)

@[simp] theorem matchedWitnessBlockReference_left_frequency :
    (matchedWitnessBlockReference C p b hb outside σ a J w P Q i r).leftRoot.frequency = i.1.val := rfl

@[simp] theorem matchedWitnessBlockReference_right_frequency :
    (matchedWitnessBlockReference C p b hb outside σ a J w P Q i r).rightRoot.frequency = i.1.val := rfl

theorem matchedWitnessBlockReference_giants :
    RootGiantsAgree (matchedWitnessBlockReference C p b hb outside σ a J w P Q i r).left.history
      (matchedWitnessBlockReference C p b hb outside σ a J w P Q i r).right.history := by
  constructor <;> simp only [MatchedBlockReference.left_root,MatchedBlockReference.right_root] <;> rfl

end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
