import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterBackground
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalExpectations

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkSourceDisintegration
open HistoryBulkActualPrincipalBlockFamily HistoryBulkUniversalPatternAggregation
attribute [local instance] Classical.propDecidable
local instance kernelStageFubiniInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)

theorem typed_kernel_fubini
    (K : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p →
        SelectedBulkSample C l → ℂ)
    (hK : ∀p o u,
      (if Function.Injective (fun q=>(blockType p q,outerBlocks C l p o q)) then K p o u else 0)=K p o u) :
    (∑p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      ∑o,(outerMass C l p o:ℂ)*(∏q : Block p,((outerBlocks C l p o q).val:ℂ))*
        (selectedBulkPrior C l).cmean (K p o)) =
      (backgroundPrior C l).cmean (fun bg=>(selectedBulkPrior C l).cmean (fun u=>
        patternComplexSum C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
          (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
          (fun p b=>K p (restoreOuterBackground C l p bg b) u))) := by
  have he : ∀p o,
      (selectedBulkPrior C l).cmean (K p o)=
        if Function.Injective (fun q=>(blockType p q,outerBlocks C l p o q)) then
          (selectedBulkPrior C l).cmean (K p o) else 0 := by
    intro p o
    by_cases ht : Function.Injective (fun q=>(blockType p q,outerBlocks C l p o q))
    · rw [ite_eq_left ht]
    · rw [ite_eq_right ht]
      have hz : ∀u,K p o u=0 := by
        intro u
        simpa only [ite_eq_right ht] using (hK p o u).symm
      simp only [FinitePrior.cmean,hz,mul_zero,Finset.sum_const_zero]
  calc
    _ = ∑p,∑o,(outerMass C l p o:ℂ)*(∏q : Block p,((outerBlocks C l p o q).val:ℂ))*
        (if Function.Injective (fun q=>(blockType p q,outerBlocks C l p o q)) then
          (selectedBulkPrior C l).cmean (K p o) else 0) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro o _
      rw [←he]
    _ = (backgroundPrior C l).cmean (fun bg=>
        patternComplexSum C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
          (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
          (fun p b=>(selectedBulkPrior C l).cmean (K p (restoreOuterBackground C l p bg b)))) :=
      outer_pattern_sum_eq_background_cmean C l _
    _ = _ := by
      apply congrArg (backgroundPrior C l).cmean
      funext bg
      unfold patternComplexSum
      simp_rw [FinitePrior.cmean_sum]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro b _
      rw [FinitePrior.cmean_mul_left]
      by_cases ht : Function.Injective (fun q=>(blockType p q,b q))
      · simp only [ite_eq_left ht]
      · simp only [ite_eq_right ht,FinitePrior.cmean,mul_zero,Finset.sum_const_zero]

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage

end

end OAI
