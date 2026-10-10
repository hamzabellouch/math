import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationRootTestDensity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatchedProducts
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatchedSource
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelReplacementPointwise

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
local instance kernelDensityBasicInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
variable {f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l}
variable {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}

abbrev DensitySources (F : MatchedPrincipalBlockFamily C outside l f g p) :=
  ∀i, F.active i → HistoryBulkFibreGiantApproximation.Frame.Source (C:=C) (l:=l)

def densityFactor (F : MatchedPrincipalBlockFamily C outside l f g p)
    (X : DensitySources F) (mixed : Bool)
    (y : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p) : ℂ :=
  if hi : F.active (originalDrawOuter (fun _ : Bool=>C.giant) C.sources _ l p y) then
    if mixed then HistoryBulkFibreGiantApproximation.Frame.extractedDensity (X _ hi) else 1
  else 1

theorem norm_densityFactor_le (F : MatchedPrincipalBlockFamily C outside l f g p)
    (X : DensitySources F) (mixed : Bool) (y) : ‖densityFactor F X mixed y‖≤1 := by
  unfold densityFactor
  split
  · cases mixed
    · exact le_of_eq (norm_one : ‖(1:ℂ)‖=1)
    · exact HistoryBulkFibreGiantApproximation.Frame.norm_extractedDensity_le _
  · exact le_of_eq (norm_one : ‖(1:ℂ)‖=1)

def densityPrincipalProductTerm (symbolic : Bool)
    (F : MatchedPrincipalBlockFamily C outside l f g p) (X : DensitySources F)
    (corrected mixed : Bool) (mask : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p→Prop) (y : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p) : ℂ :=
  densityFactor F X mixed y * principalProductTerm symbolic F corrected mixed mask y

def densityPrincipalDifferenceTerm
    (F : MatchedPrincipalBlockFamily C outside l f g p) (X : DensitySources F)
    (corrected mixed : Bool) (mask : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p→Prop) (y : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p) : ℂ :=
  densityFactor F X mixed y * principalDifferenceTerm F corrected mixed mask y

def densityPrincipalProductMean (symbolic : Bool)
    (F : MatchedPrincipalBlockFamily C outside l f g p) (X : DensitySources F)
    (corrected mixed : Bool) (mask : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p→Prop) : ℂ :=
  ∑y : OriginalDraw (fun _ : Bool=>C.giant) C.sources
    (Template.initial (2*(bulkSize k L/2)) k) l p,
    (originalDrawMass (fun _ : Bool=>C.giant) C.sources _ l p y:ℂ)*
      densityPrincipalProductTerm symbolic F X corrected mixed mask y

def densityPrincipalDifferenceMean
    (F : MatchedPrincipalBlockFamily C outside l f g p) (X : DensitySources F)
    (corrected mixed : Bool) (mask : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p→Prop) : ℂ :=
  ∑y : OriginalDraw (fun _ : Bool=>C.giant) C.sources
    (Template.initial (2*(bulkSize k L/2)) k) l p,
    (originalDrawMass (fun _ : Bool=>C.giant) C.sources _ l p y:ℂ)*
      densityPrincipalDifferenceTerm F X corrected mixed mask y

lemma densityPrincipalProductTerm_sub
    (F : MatchedPrincipalBlockFamily C outside l f g p) (X : DensitySources F)
    (corrected mixed : Bool) (mask) (y) :
    densityPrincipalProductTerm false F X corrected mixed mask y-
      densityPrincipalProductTerm true F X corrected mixed mask y=
      densityPrincipalDifferenceTerm F X corrected mixed mask y := by
  simp only [densityPrincipalProductTerm,densityPrincipalDifferenceTerm,←mul_sub,principalProductTerm_sub]

theorem densityPrincipalProductMean_sub
    (F : MatchedPrincipalBlockFamily C outside l f g p) (X : DensitySources F)
    (corrected mixed : Bool) (mask) :
    densityPrincipalProductMean false F X corrected mixed mask-
      densityPrincipalProductMean true F X corrected mixed mask=
      densityPrincipalDifferenceMean F X corrected mixed mask := by
  simp only [densityPrincipalProductMean,densityPrincipalDifferenceMean,
    ←Finset.sum_sub_distrib,←mul_sub,densityPrincipalProductTerm_sub]

lemma norm_densityPrincipalDifferenceTerm_le
    (F : MatchedPrincipalBlockFamily C outside l f g p) (X : DensitySources F)
    (corrected mixed : Bool) (mask) (y) :
    ‖densityPrincipalDifferenceTerm F X corrected mixed mask y‖≤
      ‖principalDifferenceTerm F corrected mixed mask y‖ := by
  rw [densityPrincipalDifferenceTerm,norm_mul]
  exact (mul_le_mul_of_nonneg_right (norm_densityFactor_le F X mixed y) (norm_nonneg _)).trans_eq (one_mul _)

end Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatched

end

end OAI
