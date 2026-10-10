import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyMatchedFactory
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterEquiv

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryPairReferenceSourceTransport
open HistoryBulkSourceDisintegration HistoryPairKernelProductReplacement
attribute [local instance] Classical.propDecidable
local instance actualPrincipalMatchedMeanInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
  {f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  (F : MatchedPrincipalBlockFamily C outside l f g p) (corrected mixed : Bool)

def matchedOriginalPrincipalFlagTerm
    (y : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (u : SelectedBulkSample C l) : ℝ :=
  if ho : F.active o then
    (rightRootSupportIndicator (F.reference o ho) (fun _=>C.giant) y *
      ‖(F.principal o ho).value corrected mixed u‖) *
      family (F.reference o ho).left (F.reference o ho).right
        (originalDrawValues (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y ∘
        (typedSourceEquivMatched (F.reference o ho).left (F.reference o ho).right p
          (F.reference o ho).natDraw (F.reference o ho).slot_values (F.reference o ho).root_matching).symm)
  else 0

def matchedWeightedFamilyTerm
    (y : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p) : ℝ :=
  if hy : F.active (originalDrawOuter (fun _=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p y) then
    F.weight corrected mixed y * family
      (F.reference _ hy).left (F.reference _ hy).right
      (originalDrawValues (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y ∘
        (typedSourceEquivMatched (F.reference _ hy).left (F.reference _ hy).right p
          (F.reference _ hy).natDraw (F.reference _ hy).slot_values (F.reference _ hy).root_matching).symm)
  else 0

theorem matchedWeightedFamilyTerm_eq
    (y : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p) :
    matchedWeightedFamilyTerm F corrected mixed y=matchedOriginalPrincipalFlagTerm F corrected mixed y
      (originalDrawOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y)
      (originalDrawBulk C l p y) := by
  unfold matchedWeightedFamilyTerm matchedOriginalPrincipalFlagTerm
  by_cases h : F.active (originalDrawOuter (fun _=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p y)
  · rw [dite_eq_left h,dite_eq_left h,F.weight_eq_guarded_principal_norm corrected mixed y h]
  · rw [dite_eq_right h,dite_eq_right h]

def matchedOuterPrincipalFlagTerm
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (u : SelectedBulkSample C l) : ℝ :=
  matchedOriginalPrincipalFlagTerm F corrected mixed (restoreOriginalDraw C l p o u) o u

def matchedOuterPrincipalFlagMean : ℝ :=
  ∑o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p,
    outerMass C l p o * (selectedBulkPrior C l).mean (matchedOuterPrincipalFlagTerm F corrected mixed o)

theorem matched_mean_eq_outerPrincipalFlagMean :
    F.mean corrected mixed=matchedOuterPrincipalFlagMean F corrected mixed := by
  calc
    F.mean corrected mixed = ∑y : OriginalDraw (fun _=>C.giant) C.sources
        (Template.initial (2*(bulkSize k L/2)) k) l p,
      originalDrawMass (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y *
        matchedOriginalPrincipalFlagTerm F corrected mixed y
          (originalDrawOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y)
          (originalDrawBulk C l p y) := by
      apply Finset.sum_congr rfl
      intro y _
      exact congrArg (fun z=>originalDrawMass (fun _=>C.giant) C.sources
        (Template.initial (2*(bulkSize k L/2)) k) l p y*z) (matchedWeightedFamilyTerm_eq F corrected mixed y)
    _ = _ := by
      rw [original_weighted_sum_eq_outer_mean C l p]
      unfold matchedOuterPrincipalFlagMean
      apply Finset.sum_congr rfl
      intro o _
      congr 1
      apply congrArg (selectedBulkPrior C l).mean
      funext u
      rw [originalDrawOuter_restore,originalDrawBulk_restore]
      rfl

end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
