import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageFamily
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStagePattern

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamily
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantApproximation HistoryBulkFibreOriginalReference
open HistoryBulkPrincipalBSquareReplacement HistoryRepresentativeSourceSeparation
open HistoryBulkReferencePeriodicMeanSource HistoryBulkUniversalPatternAggregation
open HistoryBulkActualPrincipalKernelStage
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (J : Background C l → Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
    SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
  (hw : ∀r,0≤w r) (hpos : ∀r,w r≠0 → 0<P r ∧ 0<Q r)
  (hcell : ∀r,w r≠0 → 0<P r ∧ 0<Q r ∧
    |Real.log (P r:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q r:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hp : ∀q∈outside,q.Prime)
  (hAd : ∀r : Frame (l:=l) C outside, PairAdmissible r.left r.right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))

theorem background_probability_expression_eq_kernel_mean (corrected mixed : Bool) :
    (backgroundPrior C l).cmean (fun bg=>(selectedBulkPrior C l).cmean (fun u=>
      expression C outside σ (J bg) w P Q hactual hl houtside hw hpos hcell hp hAd hout hV bg u i
        true corrected mixed)) =
    ∑p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      selectedKernelMean C p outside σ (fun o=>J (outerGiants C l p o,outerNonbulk C l p o))
        w P Q hactual hl houtside hw hpos hcell hout hp hV i.1 i.2.1 i.2.2 false corrected mixed := by
  rw [sum_selectedKernelMean_eq_background]
  apply congrArg (backgroundPrior C l).cmean
  funext bg
  rw [mean_expression_probability_eq_kernel_pattern]
  apply congrArg (selectedBulkPrior C l).cmean
  funext u
  apply congrArg (patternComplexSum C.sources _ _)
  funext p b
  rfl

theorem background_probability_rootExpression_eq_kernel_sum (corrected mixed : Bool) :
    (backgroundPrior C l).cmean (fun bg=>(selectedBulkPrior C l).cmean (fun u=>
      rootExpression C outside σ (J bg) w P Q hactual hl houtside hw hpos hcell hp hAd hout hV bg u
        true corrected mixed)) =
    ∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
      ∑p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
        selectedKernelMean C p outside σ (fun o=>J (outerGiants C l p o,outerNonbulk C l p o))
          w P Q hactual hl houtside hw hpos hcell hout hp hV i.1 i.2.1 i.2.2 false corrected mixed := by
  unfold rootExpression
  simp_rw [FinitePrior.cmean_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact background_probability_expression_eq_kernel_mean C outside σ J w P Q hactual hl houtside hw hpos
    hcell hp hAd hout hV i corrected mixed

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamily

end

end OAI
