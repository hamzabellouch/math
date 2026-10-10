import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportActualPrincipalPlainPrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceNewModuliSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSourcePrime

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
open HistoryPrincipalIntegralAverage
variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz depth L E) (outside : List ℕ)

structure Frame where
  leftSource : SourceAssignment C.sources (Template.current
    (Template.initial (2*(bulkSize depth L/2)) depth) l)
  rightSource : SourceAssignment C.sources (Template.current
    (Template.initial (2*(bulkSize depth L/2)) depth) l)
  s : ℤ
  t : ℤ
  P : ℤ
  Q : ℤ
  leftChoices : HistoryChoices C.sources (Template.initial (2*(bulkSize depth L/2)) depth)
    (frequencyBound Bs BD Bz depth L) l
  rightChoices : HistoryChoices C.sources (Template.initial (2*(bulkSize depth L/2)) depth)
    (frequencyBound Bs BD Bz depth L) l
  left_mass : (assignmentPrior C.sources _).mass leftSource≠0
  right_mass : (assignmentPrior C.sources _).mass rightSource≠0
  left_choices_mass : choicesMass C.sources _ _ l leftChoices≠0
  right_choices_mass : choicesMass C.sources _ _ l rightChoices≠0
  plus_pos : 0<P
  minus_pos : 0<Q
  plus_cell : |Real.log (P:ℝ)-(C.giantCenter:ℝ)|≤1
  minus_cell : |Real.log (Q:ℝ)-(C.giantCenter:ℝ)|≤1
  left_supported : (assignedHistory C.sources _ (frequencyBound Bs BD Bz depth L) l
    s P.toNat Q.toNat leftSource leftChoices).Supported (frequencyBound Bs BD Bz depth L) outside
  right_supported : (assignedHistory C.sources _ (frequencyBound Bs BD Bz depth L) l
    t P.toNat Q.toNat rightSource rightChoices).Supported (frequencyBound Bs BD Bz depth L) outside
  matching : RootMatching
    (assignedHistory C.sources _ (frequencyBound Bs BD Bz depth L) l
      s P.toNat Q.toNat leftSource leftChoices)
    (assignedHistory C.sources _ (frequencyBound Bs BD Bz depth L) l
      t P.toNat Q.toNat rightSource rightChoices)
  outside_primes : ∀q∈outside,q.Prime

namespace Frame
variable {C outside} (r : Frame (l:=l) C outside)

def left := assignedHistory C.sources _ (frequencyBound Bs BD Bz depth L) l
  r.s r.P.toNat r.Q.toNat r.leftSource r.leftChoices
def right := assignedHistory C.sources _ (frequencyBound Bs BD Bz depth L) l
  r.t r.P.toNat r.Q.toNat r.rightSource r.rightChoices

abbrev Source := SourceAssignment C.sources (Template.current
  (Template.initial (2*(bulkSize depth L/2)) depth) l)
abbrev Slots := Fin (2^l)×Fin (2*(bulkSize depth L/2))

def newLeft (x : Source (C:=C) (l:=l)) := assignedHistory C.sources _
  (frequencyBound Bs BD Bz depth L) l r.s 1 1 x r.leftChoices
def newRight (y : Source (C:=C) (l:=l)) := assignedHistory C.sources _
  (frequencyBound Bs BD Bz depth L) l r.t 1 1 y r.rightChoices

def scalar (x : Source (C:=C) (l:=l)) : (Bool→ℝ)→ℂ :=
  fun u=>jointScalar C (bulkSize depth L/2) r.left r.right r.left_supported r.right_supported
    (boolEquiv r.left r.right)
    (orderedEquiv (2*(bulkSize depth L/2)) depth r.left r.right r.left_supported
      (root_matches (assignedLabels C.sources _ _ l r.s r.P.toNat r.Q.toNat r.leftSource r.leftChoices)))
    u (orderedSourceValues C.sources (2*(bulkSize depth L/2)) depth l x)

def fixedB (x : Source (C:=C) (l:=l)) : PairKey r.left r.right→ℤ :=
  integerInsertOrderedGiants (2*(bulkSize depth L/2)) depth r.left r.right r.left_supported
    (root_matches (assignedLabels C.sources _ _ l r.s r.P.toNat r.Q.toNat r.leftSource r.leftChoices))
    (orderedIntegerSourceValues C.sources (2*(bulkSize depth L/2)) depth l x) (fun _=>0)

def residueTest (σ : Equiv.Perm (Slots (depth:=depth) (L:=L) (l:=l)))
    (x y : Source (C:=C) (l:=l)) :=
  newReferenceResidueTest d depth r.left r.right r.left_supported r.right_supported
    (r.newLeft x) (r.newRight y) σ
    (sourceBulkUnits (frequencyModulus r.left r.right (depth+2)) C.sources
      (2*(bulkSize depth L/2)) depth l x) (r.fixedB x) (rootResidueIndicator (r.newLeft x))

def periodic (σ : Equiv.Perm (Slots (depth:=depth) (L:=L) (l:=l)))
    (x y : Source (C:=C) (l:=l)) : ℂ :=
  guardedPeriodicSourcePrimeMean C.giantCenter ∅ C.giantPositive
    (newComparisonModulus (r.newLeft x) r.left r.right outside depth)
    (r.residueTest σ x y) (r.scalar x)

def giantIntegral (x : Source (C:=C) (l:=l)) : ℂ :=
  primeIntegral (fun _ : Bool=>C.giantCenter-1) (fun _=>C.giantCenter+1)
    (fun _=>logCellMass C.giantCenter ∅) (primeCutoff C.giantCenter (r.scalar x))

def principal (σ : Equiv.Perm (Slots (depth:=depth) (L:=L) (l:=l)))
    (x y : Source (C:=C) (l:=l)) : ℂ := by
  letI : NeZero outside.prod := ⟨(outsideModulus_pos r.outside_primes).ne'⟩
  letI : NeZero (frequencyModulus r.left r.right (depth+2)) :=
    ⟨(frequencyModulus_pos r.left r.right r.left_supported r.right_supported (depth+2)).ne'⟩
  letI : NeZero (representativeModulus r.left r.right) :=
    ⟨(representativeModulus_pos r.left r.right r.left_supported r.right_supported).ne'⟩
  exact r.giantIntegral x *
    (average (fun z : UnitPair outside.prod=>residuePairSpectator (residueTransform d)
      outside outside.prod (r.newLeft x) (r.newRight y) (z.1,z.2)) *
    average (fun z : UnitPair (frequencyModulus r.left r.right (depth+2))=>
      independentRTest depth r.left r.right σ
        ((z.1:ZMod (frequencyModulus r.left r.right (depth+2))),
          (z.2:ZMod (frequencyModulus r.left r.right (depth+2))))
        (sourceBulkUnits (frequencyModulus r.left r.right (depth+2)) C.sources
          (2*(bulkSize depth L/2)) depth l x)) *
    average (fun z : UnitPair (representativeModulus r.left r.right)=>
      primeResidueIndicatorAt r.left r.right r.left_supported r.right_supported (r.fixedB x) (z.1,z.2)))

def sourceMean (σ : Equiv.Perm (Slots (depth:=depth) (L:=L) (l:=l)))
    (x y : Source (C:=C) (l:=l)) : ℂ :=
  primeMean C.giant (HistoryBulkIndependentReferenceTerm.orderedReferenceTerm C
    (frequencyBound Bs BD Bz depth L) outside l depth σ r.leftSource r.rightSource x y
    r.s r.t r.P.toNat r.Q.toNat r.leftChoices r.rightChoices r.left_supported r.right_supported
    (bulkSize depth L/2) (bulkSize depth L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter
    (fun _ _=>1))

end Frame
end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

end

end OAI
