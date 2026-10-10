import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterBackgroundMass
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkSourceDisintegration
open HistoryBulkUniversalPatternAggregation
attribute [local instance] Classical.propDecidable
local instance outerBackgroundPatternsInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ)

theorem outer_jacobian_sum_eq_background_cmean
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (F : OriginalOuter (fun _=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p → ℂ) :
    (∑o,(outerMass C l p o:ℂ)*(∏q : Block p,((outerBlocks C l p o q).val:ℂ))*F o) =
      (backgroundPrior C l).cmean (fun bg=>∑b,
        (patternWeight C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
          p b:ℂ)*F (restoreOuterBackground C l p bg b)) := by
  simp only [mul_assoc]
  rw [outer_weighted_sum_eq_background_cmean C l p]
  simp only [patternWeight,Complex.ofReal_mul,Complex.ofReal_prod,Complex.ofReal_natCast,
    outerBlocks_restoreOuterBackground,mul_assoc]

theorem outer_pattern_sum_eq_background_cmean
    (F : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      OriginalOuter (fun _=>C.giant) C.sources
        (Template.initial (2*(bulkSize k L/2)) k) l p → ℂ) :
    (∑p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      ∑o,(outerMass C l p o:ℂ)*(∏q : Block p,((outerBlocks C l p o q).val:ℂ))*
        (if Function.Injective (fun q=>(blockType p q,outerBlocks C l p o q)) then F p o else 0)) =
      (backgroundPrior C l).cmean (fun bg=>
        patternComplexSum C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
          (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
          (fun p b=>F p (restoreOuterBackground C l p bg b))) := by
  simp_rw [outer_jacobian_sum_eq_background_cmean C l]
  simp only [outerBlocks_restoreOuterBackground,FinitePrior.cmean,patternComplexSum,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
