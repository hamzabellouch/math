import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSourceCorrectedMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSourceMixedActual

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
open Construction Conclusion HistoryGiantReferenceMean HistoryPairBulkTransport
open HistoryBulkReferenceNewModuli HistoryBulkGiantPrincipalTransport
open HistoryCRTIntegration HistoryPairBulkCoordinates HistoryPairGiantCoordinates
open HistoryBulkReferenceScalarCoordinates HistoryBulkSpectatorReferenceRaw
open HistoryBulkReferenceTests HistoryBulkReferencePeriodicMeanSource
open HistoryGiantWeightedPriorReplacement HistoryGiantPriorGrid ResidueHaar
open HistorySignedSpectatorCRT HistorySignedXiTransport HistoryPairPattern
open HistoryBulkGiantCorrectedBounds HistoryBulkCorrectedXiBounds
open HistorySymbolicEncoding HistorySignedResidueFactorization HistoryBulkResidueNormSum
open HistoryPrincipalIntegralAverage HistoryBulkReferenceSmallMultiplier
open HistoryDiagonalSmallOriginalMean DiagonalSmallResidueNorm
open HistorySignedResidueWeightedAverages
variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz depth L E} {outside : List ℕ}
namespace Frame
variable (r : Frame (l:=l) C outside)

def mixedScalar (x : Source (C:=C) (l:=l)) : (Option Unit→ℝ)→ℂ :=
  fun u=>jointScalar C (bulkSize depth L/2) r.left r.right r.left_supported r.right_supported
    (optionEquiv r.left r.right)
    (orderedEquiv (2*(bulkSize depth L/2)) depth r.left r.right r.left_supported
      (root_matches (assignedLabels C.sources _ _ l r.s r.P.toNat r.Q.toNat r.leftSource r.leftChoices)))
    u (orderedSourceValues C.sources (2*(bulkSize depth L/2)) depth l x)

def correctedMixedScalar (x : Source (C:=C) (l:=l)) : (Option Unit→ℝ)→ℂ :=
  fun u=>jointCorrectedScalar C (bulkSize depth L/2) r.left r.right r.left_supported r.right_supported
    (optionEquiv r.left r.right)
    (orderedEquiv (2*(bulkSize depth L/2)) depth r.left r.right r.left_supported
      (root_matches (assignedLabels C.sources _ _ l r.s r.P.toNat r.Q.toNat r.leftSource r.leftChoices)))
    u (orderedSourceValues C.sources (2*(bulkSize depth L/2)) depth l x)

def mixedResidueTest (σ : Equiv.Perm (Slots (depth:=depth) (L:=L) (l:=l)))
    (x y : Source (C:=C) (l:=l))
    (hu : SmallUnitData outside.prod 1 1 (currentOuterSlots C x) (currentRemainingSlots C x) r.s) :=
  newReferenceResidueTest d depth r.left r.right r.left_supported r.right_supported
    (r.newLeft x) (r.newRight y) σ
    (sourceBulkUnits (frequencyModulus r.left r.right (depth+2)) C.sources
      (2*(bulkSize depth L/2)) depth l x) (r.fixedB x)
    (fun z=>rootResidueIndicator (r.newLeft x) z *
      mixedExtension (currentRootSmallTest C outside x r.s r.leftChoices hu) z)

def extractedDensity (x : Source (C:=C) (l:=l)) : ℂ :=
  ((∏i : Fin (currentOuterSlots C x).length,
    ((((currentOuterSlots C x)[i].value-1:ℕ):ℝ)/(currentOuterSlots C x)[i].value):ℝ):ℂ)

def mixedBlockAverage (σ : Equiv.Perm (Slots (depth:=depth) (L:=L) (l:=l)))
    (x y : Source (C:=C) (l:=l)) : ℂ := by
  letI : NeZero outside.prod := ⟨(outsideModulus_pos r.outside_primes).ne'⟩
  letI : NeZero (frequencyModulus r.left r.right (depth+2)) :=
    ⟨(frequencyModulus_pos r.left r.right r.left_supported r.right_supported (depth+2)).ne'⟩
  letI : NeZero (representativeModulus r.left r.right) :=
    ⟨(representativeModulus_pos r.left r.right r.left_supported r.right_supported).ne'⟩
  exact extractedDensity x *
    average (fun z : MixedPair outside.prod=>residuePairSpectator (residueTransform d)
      outside outside.prod (r.newLeft x) (r.newRight y) (z.1,z.2)) *
    average (fun z : MixedPair (frequencyModulus r.left r.right (depth+2))=>
      independentRTest depth r.left r.right σ
        ((z.1:ZMod (frequencyModulus r.left r.right (depth+2))),
          (z.2:ZMod (frequencyModulus r.left r.right (depth+2))))
        (sourceBulkUnits (frequencyModulus r.left r.right (depth+2)) C.sources
          (2*(bulkSize depth L/2)) depth l x)) *
    average (fun z : MixedPair (representativeModulus r.left r.right)=>
      primeResidueIndicatorAt r.left r.right r.left_supported r.right_supported (r.fixedB x) (z.1,z.2))

def periodicMixed (σ : Equiv.Perm (Slots (depth:=depth) (L:=L) (l:=l)))
    (x y : Source (C:=C) (l:=l))
    (hu : SmallUnitData outside.prod 1 1 (currentOuterSlots C x) (currentRemainingSlots C x) r.s) : ℂ :=
  guardedPeriodicSourceMixedMean C.giantCenter ∅ C.giantPositive
    (newComparisonModulus (r.newLeft x) r.left r.right outside depth)
    (r.mixedResidueTest σ x y hu) (r.mixedScalar x)

def principalMixed (σ : Equiv.Perm (Slots (depth:=depth) (L:=L) (l:=l)))
    (x y : Source (C:=C) (l:=l)) : ℂ :=
  mixedIntegral (C.giantCenter-1) (C.giantCenter+1) C.giantCenter smoothPartition
    (fun _ : Unit=>C.giantCenter-1) (fun _=>C.giantCenter+1)
    (fun _=>logCellMass C.giantCenter ∅)
    (mixedGiantPrimeTest C.giantCenter (r.mixedScalar x)) * r.mixedBlockAverage σ x y

def sourceMeanMixed (σ : Equiv.Perm (Slots (depth:=depth) (L:=L) (l:=l)))
    (x y : Source (C:=C) (l:=l)) : ℂ :=
  mixedMean C.giantCenter C.giant
    (HistoryBulkIndependentReferenceTerm.orderedReferenceTerm C
      (frequencyBound Bs BD Bz depth L) outside l depth σ r.leftSource r.rightSource x y
      r.s r.t r.P.toNat r.Q.toNat r.leftChoices r.rightChoices r.left_supported r.right_supported
      (bulkSize depth L/2) (bulkSize depth L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter
      (fun P Q=>(smallMultiplier C outside x r.s P Q:ℂ)))

def periodicCorrectedMixed (σ : Equiv.Perm (Slots (depth:=depth) (L:=L) (l:=l)))
    (x y : Source (C:=C) (l:=l))
    (hu : SmallUnitData outside.prod 1 1 (currentOuterSlots C x) (currentRemainingSlots C x) r.s) : ℂ :=
  guardedPeriodicSourceMixedMean C.giantCenter ∅ C.giantPositive
    (newComparisonModulus (r.newLeft x) r.left r.right outside depth)
    (r.mixedResidueTest σ x y hu) (r.correctedMixedScalar x)

def principalCorrectedMixed (σ : Equiv.Perm (Slots (depth:=depth) (L:=L) (l:=l)))
    (x y : Source (C:=C) (l:=l)) : ℂ :=
  mixedIntegral (C.giantCenter-1) (C.giantCenter+1) C.giantCenter smoothPartition
    (fun _ : Unit=>C.giantCenter-1) (fun _=>C.giantCenter+1)
    (fun _=>logCellMass C.giantCenter ∅)
    (mixedGiantPrimeTest C.giantCenter (r.correctedMixedScalar x)) * r.mixedBlockAverage σ x y

def sourceMeanCorrectedMixed (σ : Equiv.Perm (Slots (depth:=depth) (L:=L) (l:=l)))
    (x y : Source (C:=C) (l:=l)) : ℂ :=
  mixedMean C.giantCenter C.giant
    (HistoryBulkIndependentReferenceTerm.orderedReferenceTerm C
      (frequencyBound Bs BD Bz depth L) outside l depth σ r.leftSource r.rightSource x y
      r.s r.t r.P.toNat r.Q.toNat r.leftChoices r.rightChoices r.left_supported r.right_supported
      (bulkSize depth L/2) (bulkSize depth L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter
      (fun P Q=>(smallMultiplier C outside x r.s P Q:ℂ) * HistoryGiantOriginalMeanFactorization.counterpart C y Q))

end Frame
end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

end

end OAI
