import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorAmplitude
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesOrder
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationMatchedReference

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairPattern HistoryPairSmoothXi HistoryPairBulkCoordinates HistoryPairGiantCoordinates
open HistoryProductWindows HistoryActiveCoordinates HistoryBulkPrincipalCollisionError HistoryBulkReplacementGeometry
attribute [local instance] Classical.propDecidable
local instance matchedPrincipalDataInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}

structure MatchedPrincipalReferenceData (C : InitialSourceChoice d Bs BD Bz k L E)
    {outside : List ℕ} {l : ℕ}
    {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
    (R : MatchedBlockReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) outside l p) where
  leftSource : SourceBounds (bulkSize k L/2) k C.giantCenter (C.cells.center (bulkSize k L/2))
    R.left.history (leftMap R.left.history R.right.history)
    (giantCoordinates R.left.history R.right.history) (pairBackground R.left.history R.right.history)
    (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1)
  rightSource : SourceBounds (bulkSize k L/2) k C.giantCenter (C.cells.center (bulkSize k L/2))
    R.right.history (rightMap R.left.history R.right.history)
    (giantCoordinates R.left.history R.right.history) (pairBackground R.left.history R.right.history)
    (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1)
  s : ℕ
  outsideLength : outside.length=2*s
  outsidePrime : ∀q∈outside,q.Prime
  outsideFrequency : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q
  permutation : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))
  K : ℕ
  independent : Bool

namespace MatchedPrincipalReferenceData
variable {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ} {l : ℕ}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {R : MatchedBlockReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
    (frequencyBound Bs BD Bz k L) outside l p}

def amplitude (P : MatchedPrincipalReferenceData C R)
    (u : (Fin (2^l) × Fin (2*(bulkSize k L/2)))→C.bulk.Sample) :
    PrincipalAmplitudeData C outside l where
  left := R.left.history
  right := R.right.history
  leftSupported := R.left.supported
  rightSupported := R.right.supported
  leftLabels := R.left.labels
  rightLabels := R.right.labels
  rootMatching := R.root_matching
  leftSource := P.leftSource
  rightSource := P.rightSource
  s := P.s
  outsideLength := P.outsideLength
  outsidePrime := P.outsidePrime
  outsideFrequency := P.outsideFrequency
  primeEquiv := boolEquiv _ _
  mixedEquiv := optionEquiv _ _
  bulkEquiv := orderedEquiv (2*(bulkSize k L/2)) k _ _ R.left.supported (by
    rw [R.left_root]
    exact R.leftMatch)
  permutation := P.permutation
  K := P.K
  residue := fun i => Characters.Template.unitConvention
    ((u i).val : ZMod (bulkModulus R.left.history R.right.history outside P.K))
  independent := P.independent

def value (P : MatchedPrincipalReferenceData C R) (corrected mixed : Bool)
    (u : (Fin (2^l) × Fin (2*(bulkSize k L/2)))→C.bulk.Sample) : ℂ :=
  (P.amplitude u).value corrected mixed u

@[simp] theorem amplitude_left (P : MatchedPrincipalReferenceData C R) (u) :
    (P.amplitude u).left=R.left.history := rfl
@[simp] theorem amplitude_right (P : MatchedPrincipalReferenceData C R) (u) :
    (P.amplitude u).right=R.right.history := rfl

theorem amplitude_residue_coe (P : MatchedPrincipalReferenceData C R) (u)
    (i : Fin (2^l) × Fin (2*(bulkSize k L/2)))
    (hi : IsUnit ((u i).val : ZMod (bulkModulus R.left.history R.right.history outside P.K))) :
    ((P.amplitude u).residue i).val=
      ((u i).val : ZMod (bulkModulus R.left.history R.right.history outside P.K)) := by
  change ((Characters.Template.unitConvention _).val : ZMod _)=_
  unfold Characters.Template.unitConvention
  split
  · exact IsUnit.unit_spec _
  · contradiction

end MatchedPrincipalReferenceData
end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
