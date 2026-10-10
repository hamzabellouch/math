import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationSelectedProducer
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationSelectedReferenceMetadata

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction Construction.CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceCoordinates HistoryPairBulkTransport
attribute [local instance] Classical.propDecidable
local instance selectedFamilyDataInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

structure ActiveBlockFamily (giants : Bool→PrimeSource) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ)
    (f g : FrequencyChoices V l) (p : Pattern (pairedHistoryType seed l)) where
  Outer : Type
  outer : OriginalDraw giants sources seed l p → Outer
  active : Outer → Prop
  reference : (i : Outer) → active i → BlockReference sources seed V outside l p
  leftRootFrequency : ℤ
  rightRootFrequency : ℤ
  leftRootFrequency_eq : ∀i hi,(reference i hi).leftRoot.frequency=leftRootFrequency
  rightRootFrequency_eq : ∀i hi,(reference i hi).rightRoot.frequency=rightRootFrequency
  leftFrequency_eq : ∀i hi,(reference i hi).leftFrequency=f
  rightFrequency_eq : ∀i hi,(reference i hi).rightFrequency=g
  permutation : Equiv.Perm (Fin (Template.current seed l).length)
  rootAligned : ∀i hi t,
    coordinateSample seed (reference i hi).right.history (reference i hi).right.labels (.inr (.inl t))=
    coordinateSample seed (reference i hi).left.history (reference i hi).left.labels (.inr (.inl (permutation t)))
  weight : OriginalDraw giants sources seed l p → ℝ

namespace ActiveBlockFamily
variable {giants : Bool→PrimeSource} {sources : SourceFamily} {seed : List SourceSlot}
  {V : ℕ→ℕ} {outside : List ℕ} {l : ℕ} {f g : FrequencyChoices V l}
  {p : Pattern (pairedHistoryType seed l)}
  (F : ActiveBlockFamily giants sources seed V outside l f g p)

def mean : ℝ := activeSourceMean giants p F.outer F.active
  (fun i hi=>(F.reference i hi).left) (fun i hi=>(F.reference i hi).right)
  (fun i hi=>(F.reference i hi).natDraw) (fun i hi=>(F.reference i hi).slot_values)
  (fun i hi=>(F.reference i hi).root_perm) F.weight

def WeightBound (A : ℝ) : Prop :=
  ∀y,F.active (F.outer y) → originalDrawMass giants sources seed l p y ≠ 0 → F.weight y ≤ A

theorem sameLeft (i : F.Outer) (hi : F.active i) (j : F.Outer) (hj : F.active j) :
    (F.reference i hi).left.SameFrequencies (F.reference j hj).left := by
  constructor
  · exact (F.leftRootFrequency_eq i hi).trans (F.leftRootFrequency_eq j hj).symm
  · rw [BlockReference.left_historyFrequencies,BlockReference.left_historyFrequencies,
      F.leftFrequency_eq i hi,F.leftFrequency_eq j hj]

theorem sameRight (i : F.Outer) (hi : F.active i) (j : F.Outer) (hj : F.active j) :
    (F.reference i hi).right.SameFrequencies (F.reference j hj).right := by
  constructor
  · exact (F.rightRootFrequency_eq i hi).trans (F.rightRootFrequency_eq j hj).symm
  · rw [BlockReference.right_historyFrequencies,BlockReference.right_historyFrequencies,
      F.rightFrequency_eq i hi,F.rightFrequency_eq j hj]

theorem zero_or_reference (A : ℝ) (hA : 0 ≤ A) (hw : F.WeightBound A) :
    F.mean=0 ∨ ∃y : OriginalDraw giants sources seed l p,
      originalDrawMass giants sources seed l p y ≠ 0 ∧
      ∃hy : F.active (F.outer y),F.mean ≤ A*(F.reference (F.outer y) hy).sourceMean giants := by
  exact activeSourceMean_zero_or_reference giants p F.outer F.active
    (fun i hi=>(F.reference i hi).left) (fun i hi=>(F.reference i hi).right)
    (fun i hi=>(F.reference i hi).natDraw) (fun i hi=>(F.reference i hi).slot_values)
    (fun i hi=>(F.reference i hi).root_perm) (F.sameLeft) (F.sameRight)
    F.permutation F.rootAligned
    (fun i hi j hj => (F.reference i hi).pairedDrawPattern_eq.trans (F.reference j hj).pairedDrawPattern_eq.symm)
    F.weight A hA hw

end ActiveBlockFamily
end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
