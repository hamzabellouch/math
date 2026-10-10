import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterBackgroundMass
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterEquiv
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatchedDensityBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkSourceDisintegration
open HistoryBulkActualPrincipalBlockFamily HistoryBulkPrincipalKernelReplacementMatched
attribute [local instance] Classical.propDecidable
local instance kernelStageProjectedInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
  {f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}

def projectedDensityProductTerm (symbolic : Bool)
    (F : MatchedPrincipalBlockFamily C outside l f g p) (X : DensitySources F)
    (corrected mixed : Bool) (mask : OriginalDraw (fun _=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p → Prop)
    (y : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (u : SelectedBulkSample C l) : ℂ :=
  if ho : F.active o then
    let R := F.reference o ho
    let z := referenceSample R y
    (if mixed then HistoryBulkFibreGiantApproximation.Frame.extractedDensity (X o ho) else 1) *
    (if mask y then
      (HistoryPairKernelProductReplacement.rightRootSupportIndicator R (fun _=>C.giant) y:ℂ)*
      (sampledJacobian R z:ℂ)*(F.principal o ho).value corrected mixed u *
      ((∏r : HistoryPairRepresentatives.Representative R.left.history R.right.history,
        if symbolic then HistoryPairKernelReplacement.symbolicKernel mixed R.left.history R.right.history
          R.left.supported R.right.supported r
          (z (HistoryPairRepresentativeVariables.representativeMap R.left.history R.right.history r)).toNat
        else HistoryPairKernelReplacement.actualProbability mixed R.left.history R.right.history
          R.left.supported R.right.supported r
          (z (HistoryPairRepresentativeVariables.representativeMap R.left.history R.right.history r)).toNat z:ℝ):ℂ)
    else 0)
  else 0

theorem densityPrincipalProductTerm_eq_projected (symbolic : Bool)
    (F : MatchedPrincipalBlockFamily C outside l f g p) (X : DensitySources F)
    (corrected mixed : Bool) (mask) (y) :
    densityPrincipalProductTerm symbolic F X corrected mixed mask y =
      projectedDensityProductTerm symbolic F X corrected mixed mask y
        (originalDrawOuter (fun _=>C.giant) C.sources _ l p y) (originalDrawBulk C l p y) := by
  unfold densityPrincipalProductTerm densityFactor principalProductTerm projectedDensityProductTerm
  split <;> simp_all only [mul_zero]

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage

end

end OAI
