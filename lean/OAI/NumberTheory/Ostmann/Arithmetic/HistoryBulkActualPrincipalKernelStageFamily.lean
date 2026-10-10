import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageFamilySquare
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageOption
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyFactors

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
  (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
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
  (bg : Background C l) (u : SelectedBulkSample C l)
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))

theorem expression_probability_eq_kernel_pattern
    (hu : (selectedBulkPrior C l).mass u≠0) (corrected mixed : Bool) :
    expression C outside σ J w P Q hactual hl houtside hw hpos hcell hp hAd hout hV bg u i
      true corrected mixed =
      patternComplexSum C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
        (fun p b=>selectedKernelOptionValue C p outside σ (fun _=>J) w P Q hactual hl houtside hw hpos hcell
          hout hp hV i.1 i.2.1 i.2.2 (restoreOuterBackground C l p bg b) false corrected mixed u) := by
  unfold expression densityBExpressionSum
  apply congrArg (patternComplexSum C.sources _ _)
  funext p b
  rw [densityPatternFactor_eq]
  unfold selectedTerm selectedOuter selectedKernelOptionValue
  cases hr : selectMatchedOuterReference C p (restoreOuterBackground C l p bg b)
      outside σ J w P Q i hactual hl houtside hw hpos with
  | none => rfl
  | some R =>
    exact squareTerm_true_eq_kernelTerm C outside σ J w P Q hcell hp hAd hout hV bg u i p b R hu corrected mixed

theorem mean_expression_probability_eq_kernel_pattern (corrected mixed : Bool) :
    (selectedBulkPrior C l).cmean (fun u=>
      expression C outside σ J w P Q hactual hl houtside hw hpos hcell hp hAd hout hV bg u i
        true corrected mixed) =
    (selectedBulkPrior C l).cmean (fun u=>
      patternComplexSum C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
        (fun p b=>selectedKernelOptionValue C p outside σ (fun _=>J) w P Q hactual hl houtside hw hpos hcell
          hout hp hV i.1 i.2.1 i.2.2 (restoreOuterBackground C l p bg b) false corrected mixed u)) := by
  apply FinitePrior.cmean_congr_support
  intro u hu
  exact expression_probability_eq_kernel_pattern C outside σ J w P Q hactual hl houtside hw hpos hcell
    hp hAd hout hV bg u i hu corrected mixed

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamily

end

end OAI
