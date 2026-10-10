import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelReplacementPointwise
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagPrincipalMatched

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatched
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryPairReferenceSourceTransport
open HistoryPairPattern HistoryPairRepresentatives HistoryPairRows HistoryPairKernelReplacement
open HistoryPairSourceCoordinates HistoryPairRepresentativeVariables HistoryPairKernelProductReplacement
attribute [local instance] Classical.propDecidable
local instance kernelBasicInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
variable {f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l}
variable {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}

def referenceSample
    (R : MatchedBlockReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) outside l p)
    (y : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p) : PairKey R.left.history R.right.history→ℤ :=
  originalDrawValues (fun _ : Bool=>C.giant) C.sources _ l p y ∘
    (typedSourceEquivMatched R.left R.right p R.natDraw R.slot_values R.root_matching).symm

def sampledJacobian
    (R : MatchedBlockReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) outside l p)
    (x : PairKey R.left.history R.right.history→ℤ) : ℝ :=
  ∏r : Representative R.left.history R.right.history,
    ((x (representativeMap R.left.history R.right.history r)).toNat:ℝ)

def kernelDifference (mixed : Bool)
    (R : MatchedBlockReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) outside l p)
    (x : PairKey R.left.history R.right.history→ℤ) : ℝ :=
  (∏r : Representative R.left.history R.right.history,
    actualProbability mixed R.left.history R.right.history R.left.supported R.right.supported
      r (x (representativeMap R.left.history R.right.history r)).toNat x)-
  ∏r : Representative R.left.history R.right.history,
    symbolicKernel mixed R.left.history R.right.history R.left.supported R.right.supported
      r (x (representativeMap R.left.history R.right.history r)).toNat

def principalDifferenceTerm (F : MatchedPrincipalBlockFamily C outside l f g p)
    (corrected mixed : Bool)
    (mask : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p→Prop)
    (y : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p) : ℂ :=
  if hy : F.active (originalDrawOuter (fun _ : Bool=>C.giant) C.sources _ l p y) then
    if mask y then
      let R := F.reference _ hy
      let x := referenceSample R y
      (rightRootSupportIndicator R (fun _ : Bool=>C.giant) y:ℂ)*(sampledJacobian R x:ℂ)*(F.principal _ hy).value corrected mixed (originalDrawBulk C l p y)*
        (kernelDifference mixed R x:ℂ)
    else 0
  else 0

def principalDifferenceMean (F : MatchedPrincipalBlockFamily C outside l f g p)
    (corrected mixed : Bool)
    (mask : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p→Prop) : ℂ :=
  ∑y : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p,
    (originalDrawMass (fun _ : Bool=>C.giant) C.sources _ l p y:ℂ)*
      principalDifferenceTerm F corrected mixed mask y

end Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatched

end

end OAI
