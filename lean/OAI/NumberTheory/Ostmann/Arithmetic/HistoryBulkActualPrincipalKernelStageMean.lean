import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterMass
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageMeanBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageOption

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation
open HistoryBulkActualPrincipalBlockFamily HistoryBulkPrincipalKernelReplacementMatched
open HistoryBulkReferencePeriodicMeanSource HistoryBulkFibreOriginalReference
attribute [local instance] Classical.propDecidable
local instance kernelStageMeanInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (outside : List ℕ) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (J : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p →
    Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
  (hw : ∀r,0≤w r) (hpos : ∀r,w r≠0 → 0<P r ∧ 0<Q r)
  (hcell : ∀r,w r≠0 → 0<P r ∧ 0<Q r ∧
    |Real.log (P r:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q r:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hlen : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l)
  (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l)

theorem selectedKernelMean_eq_outerOption (symbolic corrected mixed : Bool) :
    selectedKernelMean C p outside σ J w P Q hactual hl houtside hw hpos hcell
      hlen hprime hV v f g symbolic corrected mixed =
    ∑o,(outerMass C l p o:ℂ)*(∏q : Block p,((outerBlocks C l p o q).val:ℂ))*
      (selectedBulkPrior C l).cmean (fun u=>
        selectedKernelOptionValue C p outside σ J w P Q hactual hl houtside hw hpos hcell
          hlen hprime hV v f g o symbolic corrected mixed u) := by
  unfold selectedKernelMean
  rw [densityPrincipalProductMean_eq_outer_cmean (C:=C) (l:=l)]
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : outerMass C l p o=0
  · simp only [ho,Complex.ofReal_zero,zero_mul]
  · rw [mul_assoc]
    apply congrArg ((outerMass C l p o:ℂ)*·)
    rw [←FinitePrior.cmean_mul_left]
    apply FinitePrior.cmean_congr_support
    intro u hu
    exact densityPrincipalProductTerm_eq_jacobian_option (l:=l) C p outside σ J w P Q
      hactual hl houtside hw hpos hcell hlen hprime hV v f g o symbolic corrected mixed u ho hu

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage

end

end OAI
