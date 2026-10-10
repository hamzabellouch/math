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
local instance kernelStageBasicInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
  {f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}

theorem densityPrincipalProductMean_eq_outer_cmean (symbolic : Bool)
    (F : MatchedPrincipalBlockFamily C outside l f g p) (X : DensitySources F)
    (corrected mixed : Bool) (mask) :
    densityPrincipalProductMean symbolic F X corrected mixed mask =
      ∑o,(outerMass C l p o:ℂ)*(selectedBulkPrior C l).cmean (fun u=>
        densityPrincipalProductTerm symbolic F X corrected mixed mask
          (restoreOriginalDraw C l p o u)) :=
  original_weighted_sum_eq_outer_cmean C l p _

theorem densityPrincipalProductMean_eq_background_cmean (symbolic : Bool)
    (F : MatchedPrincipalBlockFamily C outside l f g p) (X : DensitySources F)
    (corrected mixed : Bool) (mask) :
    densityPrincipalProductMean symbolic F X corrected mixed mask =
      (backgroundPrior C l).cmean (fun bg=>∑b,
        ((∏q : Block p,biasedBlockWeight C.sources
          (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l) p q (b q)):ℂ)*
          (selectedBulkPrior C l).cmean (fun u=>
            densityPrincipalProductTerm symbolic F X corrected mixed mask
              (restoreOriginalDraw C l p (restoreOuterBackground C l p bg b) u))) := by
  rw [densityPrincipalProductMean_eq_outer_cmean]
  exact outer_weighted_sum_eq_background_cmean C l p _

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage

end

end OAI
