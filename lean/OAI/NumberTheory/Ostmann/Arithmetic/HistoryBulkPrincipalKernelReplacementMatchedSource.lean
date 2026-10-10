import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatchedFinite
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelProductReplacementMatched

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
local instance kernelSourceInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
variable {f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l}
variable {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}

theorem principalDifferenceTerm_le
    (F : MatchedPrincipalBlockFamily C outside l f g p) (corrected mixed : Bool)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (hroot : ∀i hi,RootGiantsAgree (F.reference i hi).left.history (F.reference i hi).right.history)
    (hV : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j))
    (mask : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p→Prop)
    (y : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p)
    (hy : originalDrawMass (fun _ : Bool=>C.giant) C.sources _ l p y≠0) :
    ‖principalDifferenceTerm F corrected mixed mask y‖ ≤
      (4*2^(Fintype.card (Block p)))*weightedFlags F corrected mixed y := by
  by_cases ha : F.active (originalDrawOuter (fun _ : Bool=>C.giant) C.sources _ l p y)
  · by_cases hm : mask y
    · let R := F.reference _ ha
      let x := referenceSample R y
      let A := (F.principal _ ha).value corrected mixed (originalDrawBulk C l p y)
      by_cases hr : RightRootSupported R (fun _ : Bool=>C.giant) y
      · have hguard : rightRootSupportIndicator R (fun _ : Bool=>C.giant) y=1 := by
          simp only [rightRootSupportIndicator,ite_eq_left hr]
        have hp : sampledJacobian R x * |kernelDifference mixed R x| ≤
            4*2^(Fintype.card (Block p))*family R.left R.right x :=
          matchedBlockReference_originalDraw_product_error C hsep mixed R (hroot _ ha)
            (fun _ : Bool=>C.giant) y hy hr hV
        simp only [principalDifferenceTerm,weightedFlags,dite_eq_left ha,ite_eq_left hm]
        rw [F.weight_eq_guarded_principal_norm corrected mixed y ha]
        change ‖(rightRootSupportIndicator R (fun _ : Bool=>C.giant) y:ℂ)*
          (sampledJacobian R x:ℂ)*A*(kernelDifference mixed R x:ℂ)‖ ≤
          (4*2^(Fintype.card (Block p)))*
            ((rightRootSupportIndicator R (fun _ : Bool=>C.giant) y*‖A‖)*family R.left R.right x)
        rw [hguard]
        simp only [Complex.ofReal_one,one_mul]
        rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
          Real.norm_eq_abs,abs_of_nonneg (sampledJacobian_nonneg R x)]
        calc
          _ = ‖A‖*(sampledJacobian R x*|kernelDifference mixed R x|) := by ring
          _ ≤ ‖A‖*(4*2^(Fintype.card (Block p))*family R.left R.right x) :=
            mul_le_mul_of_nonneg_left hp (norm_nonneg A)
          _ = _ := by ring
      · have hz : rightRootSupportIndicator (F.reference _ ha) (fun _ : Bool=>C.giant) y=0 := by
          change rightRootSupportIndicator R (fun _ : Bool=>C.giant) y=0
          simp only [rightRootSupportIndicator,ite_eq_right hr]
        simp only [principalDifferenceTerm,dite_eq_left ha,ite_eq_left hm,hz,Complex.ofReal_zero,
          zero_mul,norm_zero]
        exact mul_nonneg (by positivity) (weightedFlags_nonneg F corrected mixed y)
    · simp only [principalDifferenceTerm,dite_eq_left ha,ite_eq_right hm,norm_zero]
      exact mul_nonneg (by positivity) (weightedFlags_nonneg F corrected mixed y)
  · simp only [principalDifferenceTerm,weightedFlags,dite_eq_right ha,norm_zero,mul_zero,le_refl]

theorem principalDifferenceMean_le
    (F : MatchedPrincipalBlockFamily C outside l f g p) (corrected mixed : Bool)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (hroot : ∀i hi,RootGiantsAgree (F.reference i hi).left.history (F.reference i hi).right.history)
    (hV : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j))
    (mask : OriginalDraw (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p→Prop) :
    ‖principalDifferenceMean F corrected mixed mask‖ ≤
      (2:ℝ)^(Fintype.card (Block p))*(4*F.mean corrected mixed) := by
  exact (principalDifferenceMean_le_of_pointwise F corrected mixed mask _
    (principalDifferenceTerm_le F corrected mixed hsep hroot hV mask)).trans_eq (by ring)

end Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatched

end

end OAI
