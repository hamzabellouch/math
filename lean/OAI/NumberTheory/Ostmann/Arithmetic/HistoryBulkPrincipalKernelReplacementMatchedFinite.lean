import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatchedBasic

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
local instance kernelFiniteInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
variable {f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l}
variable {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}

lemma sampledJacobian_nonneg
    (R : MatchedBlockReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) outside l p)
    (x : PairKey R.left.history R.right.history→ℤ) : 0 ≤ sampledJacobian R x :=
  Finset.prod_nonneg (fun _ _=>Nat.cast_nonneg _)

def weightedFlags (F : MatchedPrincipalBlockFamily C outside l f g p) (corrected mixed : Bool)
    (y : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p) : ℝ :=
  if hy : F.active (originalDrawOuter (fun _ : Bool=>C.giant) C.sources _ l p y) then
    F.weight corrected mixed y * family (F.reference _ hy).left (F.reference _ hy).right
      (referenceSample (F.reference _ hy) y)
  else 0

lemma weightedFlags_nonneg (F : MatchedPrincipalBlockFamily C outside l f g p) (corrected mixed : Bool)
    (y : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p) : 0 ≤ weightedFlags F corrected mixed y := by
  unfold weightedFlags
  split
  · exact mul_nonneg (F.weight_nonneg corrected mixed y) (family_nonneg _ _ _)
  · exact le_refl _

lemma mean_eq_sum_weightedFlags (F : MatchedPrincipalBlockFamily C outside l f g p) (corrected mixed : Bool) :
    F.mean corrected mixed =
      ∑y : OriginalDraw (fun _ : Bool=>C.giant) C.sources
        (Template.initial (2*(bulkSize k L/2)) k) l p,
        originalDrawMass (fun _ : Bool=>C.giant) C.sources _ l p y * weightedFlags F corrected mixed y := rfl

lemma principalFlagMean_nonneg (F : MatchedPrincipalBlockFamily C outside l f g p) (corrected mixed : Bool) :
    0 ≤ F.mean corrected mixed := by
  rw [mean_eq_sum_weightedFlags]
  exact Finset.sum_nonneg (fun y _=>mul_nonneg
    (originalDrawMass_nonneg _ _ _ _ _ y) (weightedFlags_nonneg F corrected mixed y))

theorem principalDifferenceMean_le_of_pointwise
    (F : MatchedPrincipalBlockFamily C outside l f g p) (corrected mixed : Bool)
    (mask : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p→Prop)
    (A : ℝ)
    (h : ∀y, originalDrawMass (fun _ : Bool=>C.giant) C.sources _ l p y ≠ 0 →
      ‖principalDifferenceTerm F corrected mixed mask y‖ ≤ A*weightedFlags F corrected mixed y) :
    ‖principalDifferenceMean F corrected mixed mask‖ ≤ A*F.mean corrected mixed := by
  rw [principalDifferenceMean,mean_eq_sum_weightedFlags,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : originalDrawMass (fun _ : Bool=>C.giant) C.sources _ l p y=0
  · simp only [hy,Complex.ofReal_zero,zero_mul,mul_zero,norm_zero,le_refl]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (originalDrawMass_nonneg _ _ _ _ _ y)]
  calc
    _ ≤ originalDrawMass (fun _ : Bool=>C.giant) C.sources _ l p y *
        (A*weightedFlags F corrected mixed y) :=
      mul_le_mul_of_nonneg_left (h y hy) (originalDrawMass_nonneg _ _ _ _ _ y)
    _ = _ := by ring

end Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatched

end

end OAI
