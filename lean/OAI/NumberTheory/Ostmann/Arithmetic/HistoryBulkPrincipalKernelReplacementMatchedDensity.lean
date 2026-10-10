import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatchedDensityBasic

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
local instance kernelDensityInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
variable {f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l}
variable {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}

theorem densityPrincipalDifferenceMean_le_of_pointwise
    (F : MatchedPrincipalBlockFamily C outside l f g p) (X : DensitySources F) (corrected mixed : Bool)
    (mask : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p→Prop)
    (A : ℝ)
    (h : ∀y, originalDrawMass (fun _ : Bool=>C.giant) C.sources _ l p y ≠ 0 →
      ‖densityPrincipalDifferenceTerm F X corrected mixed mask y‖ ≤ A*weightedFlags F corrected mixed y) :
    ‖densityPrincipalDifferenceMean F X corrected mixed mask‖ ≤ A*F.mean corrected mixed := by
  rw [densityPrincipalDifferenceMean,mean_eq_sum_weightedFlags,Finset.mul_sum]
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

theorem densityPrincipalDifferenceMean_le
    (F : MatchedPrincipalBlockFamily C outside l f g p) (X : DensitySources F) (corrected mixed : Bool)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (hroot : ∀i hi,RootGiantsAgree (F.reference i hi).left.history (F.reference i hi).right.history)
    (hV : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j))
    (mask : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p→Prop) :
    ‖densityPrincipalDifferenceMean F X corrected mixed mask‖ ≤
      (2:ℝ)^(Fintype.card (Block p))*(4*F.mean corrected mixed) := by
  apply (densityPrincipalDifferenceMean_le_of_pointwise F X corrected mixed mask (4*2^(Fintype.card (Block p))) ?_).trans_eq (by ring)
  intro y hy
  exact (norm_densityPrincipalDifferenceTerm_le F X corrected mixed mask y).trans
    (principalDifferenceTerm_le F corrected mixed hsep hroot hV mask y hy)

end Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatched

end

end OAI
