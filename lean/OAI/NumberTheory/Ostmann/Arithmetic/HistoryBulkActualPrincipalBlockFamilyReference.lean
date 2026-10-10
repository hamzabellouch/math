import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilyWitness
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferencePermutation
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagPrincipal

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryCompensationRepresentativePatterns
open HistoryBulkActualRootReferenceFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreOriginalReference HistoryGiantOriginalMeanFactorization HistorySignedXiTransport
open HistoryPairPattern HistoryGiantReferenceMean
attribute [local instance] Classical.propDecidable
local instance actualPrincipalReferenceInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : BlockDraw p (CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)))
  (hb : ∀i,(expand p b i).val∈(C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l i)).candidates)

abbrev leftBlockDraws : Draws C (l:=l) :=
  fun i=>blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hb (.inl i)
abbrev rightBlockDraws : Draws C (l:=l) :=
  fun i=>blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hb (.inr i)

variable (outside : List ℕ) (a : SelectedNonbulkSample C l)
  (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
  (r : Witness C outside (Equiv.refl _) a (leftBlockDraws C p b hb) (rightBlockDraws C p b hb) J w P Q i)

def witnessRoot : State :=
  giantState (sourceState C.sources _ (fibreAssignment C a r.bulk) i.1.val) (P r.giant) (Q r.giant)

def witnessBlockReference :
    BlockReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) outside l p where
  blockDraw := b
  valid := hb
  leftRoot := witnessRoot C p b hb outside a J w P Q i r
  rightRoot := witnessRoot C p b hb outside a J w P Q i r
  leftFrequency := i.2.1
  rightFrequency := i.2.2
  leftMatch := Template.assignedSlots_matches C.sources _ (fibreAssignment C a r.bulk)
  rightMatch := Template.assignedSlots_matches C.sources _ (fibreAssignment C a r.bulk)
  leftSupported := r.supported.1
  rightSupported := by
    have h := r.supported.2
    simp only [permute_fibreAssignment,Equiv.refl_apply] at h
    exact h
  rootPerm := List.Perm.refl _

@[simp] theorem witnessBlockReference_left_frequency :
    (witnessBlockReference C p b hb outside a J w P Q i r).leftRoot.frequency=i.1.val := rfl
@[simp] theorem witnessBlockReference_right_frequency :
    (witnessBlockReference C p b hb outside a J w P Q i r).rightRoot.frequency=i.1.val := rfl

theorem witnessBlockReference_giants :
    RootGiantsAgree (witnessBlockReference C p b hb outside a J w P Q i r).left.history
      (witnessBlockReference C p b hb outside a J w P Q i r).right.history := by
  constructor <;> simp only [BlockReference.left_root,BlockReference.right_root] <;> rfl

end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
