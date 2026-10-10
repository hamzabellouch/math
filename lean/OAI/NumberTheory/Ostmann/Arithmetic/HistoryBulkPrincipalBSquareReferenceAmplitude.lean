import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorAmplitude
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceSourceBounds

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReference
open Construction CanonicalOccurrenceTransport Conclusion HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairBulkCoordinates HistoryPairGiantCoordinates
open HistoryBulkReferenceTests HistoryPairBulkTransport HistoryBulkSpectatorReferenceRaw
open HistoryBulkFibreGiantApproximation HistoryBulkPrincipalCollisionError
open HistoryGiantReferenceSourceBounds HistorySymbolicEncoding HistoryBulkReplacementGeometry
variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz depth L E} {outside : List ℕ}

def newBulk (x : Frame.Source (C:=C) (l:=l)) :
    (Fin (2^l)×Fin (2*(bulkSize depth L/2)))→C.bulk.Sample := fun u => by
  let i := (currentBulkPositionEquiv (2*(bulkSize depth L/2)) depth l).symm u
  refine ⟨(x i.val).val,?_⟩
  have hs : C.sources ((Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l)[i.val].origin)=C.bulk :=
    current_bulk_source (bulkSize depth L/2) depth l C.bulk
      (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) i
  rw [←hs]
  exact (x i.val).property

@[simp] theorem newBulk_val (x : Frame.Source (C:=C) (l:=l))
    (u : Fin (2^l)×Fin (2*(bulkSize depth L/2))) :
    ((newBulk x u).val:ℤ) = orderedIntegerSourceValues C.sources
      (2*(bulkSize depth L/2)) depth l x u := rfl

def principalAmplitude (r : Frame (l:=l) C outside) (sw : ℕ)
    (hout : outside.length=2*sw)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz depth L j<q)
    (σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l)))
    (K : ℕ) (x : Frame.Source (C:=C) (l:=l)) : PrincipalAmplitudeData C outside l := by
  have hsource := selected_reference_sourceBounds C (frequencyBound Bs BD Bz depth L) l
    r.leftSource r.rightSource r.s r.t r.leftChoices r.rightChoices r.P r.Q
    r.left_mass r.right_mass r.left_choices_mass r.right_choices_mass
    r.plus_pos r.minus_pos r.plus_cell r.minus_cell
  exact
    { left := r.left
      right := r.right
      leftSupported := r.left_supported
      rightSupported := r.right_supported
      leftLabels := (leftDraw r).labels
      rightLabels := (rightDraw r).labels
      rootMatching := r.matching
      leftSource := hsource.1
      rightSource := hsource.2
      s := sw
      outsideLength := hout
      outsidePrime := r.outside_primes
      outsideFrequency := hV
      primeEquiv := boolEquiv r.left r.right
      mixedEquiv := optionEquiv r.left r.right
      bulkEquiv := orderedEquiv (2*(bulkSize depth L/2)) depth r.left r.right r.left_supported
        (root_matches (assignedLabels C.sources _ _ l r.s r.P.toNat r.Q.toNat r.leftSource r.leftChoices))
      permutation := σ
      K := K
      residue := sourceBulkUnits (bulkModulus r.left r.right outside K) C.sources
        (2*(bulkSize depth L/2)) depth l x
      independent := true }

@[simp] theorem principalAmplitude_left (r : Frame (l:=l) C outside) (sw hout hV σ K x) :
    (principalAmplitude r sw hout hV σ K x).left=r.left := rfl
@[simp] theorem principalAmplitude_right (r : Frame (l:=l) C outside) (sw hout hV σ K x) :
    (principalAmplitude r sw hout hV σ K x).right=r.right := rfl

end Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReference

end

end OAI
