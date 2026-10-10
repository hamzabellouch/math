import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatchedBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatched
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryPairPattern HistoryPairRepresentatives
open HistoryPairKernelReplacement HistoryPairRepresentativeVariables HistoryPairKernelProductReplacement
attribute [local instance] Classical.propDecidable
local instance kernelProductsInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
variable {f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l}
variable {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}

def principalProductTerm (symbolic : Bool) (F : MatchedPrincipalBlockFamily C outside l f g p)
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
        ((∏r : Representative R.left.history R.right.history,
          if symbolic then symbolicKernel mixed R.left.history R.right.history R.left.supported R.right.supported
            r (x (representativeMap R.left.history R.right.history r)).toNat
          else actualProbability mixed R.left.history R.right.history R.left.supported R.right.supported
            r (x (representativeMap R.left.history R.right.history r)).toNat x : ℝ):ℂ)
    else 0
  else 0

def principalProductMean (symbolic : Bool) (F : MatchedPrincipalBlockFamily C outside l f g p)
    (corrected mixed : Bool)
    (mask : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p→Prop) : ℂ :=
  ∑y : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p,
    (originalDrawMass (fun _ : Bool=>C.giant) C.sources _ l p y:ℂ)*
      principalProductTerm symbolic F corrected mixed mask y

lemma principalProductTerm_sub (F : MatchedPrincipalBlockFamily C outside l f g p)
    (corrected mixed : Bool) (mask) (y) :
    principalProductTerm false F corrected mixed mask y-
      principalProductTerm true F corrected mixed mask y=
      principalDifferenceTerm F corrected mixed mask y := by
  unfold principalProductTerm principalDifferenceTerm
  split
  · split
    · simp only [Bool.false_eq_true,ite_false,ite_true,kernelDifference,Complex.ofReal_sub,mul_sub]
    · simp only [sub_self]
  · simp only [sub_self]

theorem principalProductMean_sub (F : MatchedPrincipalBlockFamily C outside l f g p)
    (corrected mixed : Bool) (mask) :
    principalProductMean false F corrected mixed mask-
      principalProductMean true F corrected mixed mask=
      principalDifferenceMean F corrected mixed mask := by
  simp only [principalProductMean,principalDifferenceMean,←Finset.sum_sub_distrib,←mul_sub,
    principalProductTerm_sub]

end Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatched

end

end OAI
