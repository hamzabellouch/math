import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferencePattern
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacementFinite

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReference
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives
open HistoryCompensationRepresentativePatterns HistoryPairVariableBSquareErrorSelected
open HistoryBulkFibreGiantApproximation HistoryPairSourceLaws HistorySymbolicEncoding
open HistoryRepresentativeSourceSeparation HistoryBulkPrincipalBSquareReplacement
open HistoryBulkPrincipalCollisionError HistoryBulkSelectedPrincipalAmplitude
open HistoryBulkGiantCorrectedBounds HistoryPrincipalIntegralAverage
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryBulkReferenceScalarCoordinates
open HistoryGiantWeightedPriorReplacement HistoryBulkSelectedIntegralReplacement
open HistoryGiantPriorGrid HistoryBulkSpectatorReferenceRaw HistoryPairBulkTransport
local instance squareReferenceSpliceInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz depth L E} {outside : List ℕ}
variable (r : Frame (l:=l) C outside) (x : Frame.Source (C:=C) (l:=l))
    (hx : (assignmentPrior C.sources _).mass x≠0)
variable (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize depth L/2)) depth) l))
    (b : BlockDraw p (CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize depth L/2)) depth) l)))
    (hslots : ∀i, (slot r.left r.right (pairedInternalEquiv
      (Template.initial (2*(bulkSize depth L/2)) depth) r.left r.right
      (leftDraw r).labels (rightDraw r).labels i)).value=(expand p b i).val)
    (had : PairAdmissible r.left r.right outside)

@[simp] theorem principalSquareReference_bMean (sw hout hV σ K) (mixed : Bool) :
    HistoryBulkPrincipalBSquareReplacement.bMean
      (principalSquareReference r x hx p b hslots had sw hout hV σ K) mixed =
        (if mixed then r.mixedBMean x else r.unitBMean x) := by
  cases mixed <;> rfl

@[simp] theorem principalSquareReference_probabilityProduct (sw hout hV σ K) (mixed : Bool) :
    HistoryBulkPrincipalBSquareReplacement.probabilityProduct
      (principalSquareReference r x hx p b hslots had sw hout hV σ K) mixed =
        (probabilityProduct r mixed x : ℂ) := rfl

def giantIntegralFactor (r : Frame (l:=l) C outside) (corrected mixed : Bool)
    (x : Frame.Source (C:=C) (l:=l)) : ℂ :=
  if mixed then
    mixedIntegral (C.giantCenter-1) (C.giantCenter+1) C.giantCenter smoothPartition
      (fun _ : Unit=>C.giantCenter-1) (fun _=>C.giantCenter+1)
      (fun _=>logCellMass C.giantCenter ∅)
      (mixedGiantPrimeTest C.giantCenter
        (if corrected then r.correctedMixedScalar x else r.mixedScalar x))
  else if corrected then
    primeGiantScalar C.giantCenter (logCellMass C.giantCenter ∅)
      (jointCorrectedScalar C (bulkSize depth L/2) r.left r.right
        r.left_supported r.right_supported (boolEquiv r.left r.right)
        (orderedEquiv (2*(bulkSize depth L/2)) depth r.left r.right r.left_supported
          (root_matches (assignedLabels C.sources _ _ l r.s r.P.toNat r.Q.toNat
            r.leftSource r.leftChoices))))
      (orderedSourceValues C.sources (2*(bulkSize depth L/2)) depth l x)
  else r.giantIntegral x

@[simp] theorem giantIntegralFactor_plain_prime :
    giantIntegralFactor r false false x=r.giantIntegral x := rfl

theorem mixed_principal_eq (corrected : Bool)
    (σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l)))
    (y : Frame.Source (C:=C) (l:=l)) :
    (if corrected then r.principalCorrectedMixed σ x y else r.principalMixed σ x y)=
      giantIntegralFactor r corrected true x * r.mixedBlockAverage σ x y := by
  cases corrected <;> rfl

theorem principalAmplitude_value_eq
    (hout : outside.length=2*(bulkSize depth L/2))
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz depth L j<q)
    (σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l)))
    (corrected mixed : Bool) :
    (principalAmplitude r (bulkSize depth L/2) hout hV σ depth x).value
      corrected mixed (newBulk x)=
        r.rootValue mixed hV σ x * giantIntegralFactor r corrected mixed x := by
  cases corrected <;> cases mixed <;> rfl

theorem principalSquareReference_value_eq
    (hout : outside.length=2*(bulkSize depth L/2))
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz depth L j<q)
    (σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l)))
    (corrected mixed : Bool) :
    (principalSquareReference r x hx p b hslots had (bulkSize depth L/2) hout hV σ depth).principal.value
      corrected mixed
      (principalSquareReference r x hx p b hslots had (bulkSize depth L/2) hout hV σ depth).newBulk=
        r.rootValue mixed hV σ x * giantIntegralFactor r corrected mixed x :=
  principalAmplitude_value_eq r x hout hV σ corrected mixed

end Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReference

end

end OAI
