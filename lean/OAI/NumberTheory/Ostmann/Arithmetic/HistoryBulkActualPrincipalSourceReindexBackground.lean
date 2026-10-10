import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterBackground
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexPattern

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkActualPrincipalBlockFamily HistoryBulkUniversalPatternAggregation
open HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalSourceReindexPattern HistoryBulkFibreGiantErrorAverage
open HistoryBulkReferenceFrequencyFamily HistoryPairSourceLaws
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)

theorem nonbulk_cmean_eq_background (F : SelectedNonbulkSample C l → ℂ) :
    (selectedNonbulkPrior C l).cmean F=(backgroundPrior C l).cmean (fun bg=>F bg.2) := by
  unfold backgroundPrior
  rw [FinitePrior.pair_cmean]
  symm
  let μ := dependentProductPrior (fun _ : Bool=>C.giant.law)
  change μ.cmean (fun _=>(selectedNonbulkPrior C l).cmean F)=_
  simp only [FinitePrior.cmean,←Finset.sum_mul,←Complex.ofReal_sum,μ.mass_total,
    Complex.ofReal_one,one_mul]

theorem originalSourceAverage_eq_backgroundPatternMean (spectator : PrimeSource)
    (F : (Fin (2*(bulkSize k L/2))→spectator.Sample) → SelectedNonbulkSample C l →
      Draws C (l:=l) → Draws C (l:=l) → RootFrequencyIndex (frequencyBound Bs BD Bz k L) l → ℂ) :
    originalSourceAverage C spectator F=
      (spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds=>
        (backgroundPrior C l).cmean (fun bg=>
          patternComplexSum C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
            (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
            (fun p b=>∑i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l,
              drawPatternValue C spectator F ds bg.2 i p b))) := by
  rw [originalSourceAverage_eq_patternMean]
  apply congrArg (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
  funext ds
  exact nonbulk_cmean_eq_background C _

theorem background_pattern_congr
    (F G : Background C l → ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      (Block p → CommonSample C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → ℂ)
    (h : ∀bg p b,outerMass C l p (restoreOuterBackground C l p bg b)≠0 →
      Function.Injective (fun q=>(blockType p q,b q)) → F bg p b=G bg p b) :
    (backgroundPrior C l).cmean (fun bg=>patternComplexSum C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l) (F bg))=
    (backgroundPrior C l).cmean (fun bg=>patternComplexSum C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l) (G bg)) := by
  classical
  apply FinitePrior.cmean_congr_support
  intro bg hbg
  unfold patternComplexSum
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hw : patternWeight C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l) p b=0
  · simp only [hw,Complex.ofReal_zero,zero_mul]
  by_cases ht : Function.Injective (fun q=>(blockType p q,b q))
  · have hp : (∏q : Block p,biasedBlockWeight C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l) p q (b q))≠0 :=
      (mul_ne_zero_iff.mp hw).1
    have ho : outerMass C l p (restoreOuterBackground C l p bg b)≠0 := by
      rw [outerMass_restoreOuterBackground]
      exact mul_ne_zero hbg hp
    rw [ite_eq_left ht,ite_eq_left ht,h bg p b ho ht]
  · simp only [ht,ite_false]

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex

end

end OAI
