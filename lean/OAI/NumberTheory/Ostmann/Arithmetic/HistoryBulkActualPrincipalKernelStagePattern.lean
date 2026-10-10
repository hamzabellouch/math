import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageFubini
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageMean

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
open HistoryBulkUniversalPatternAggregation
attribute [local instance] Classical.propDecidable
local instance kernelStagePatternInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (outside : List ℕ) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (J : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l), OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p →
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

theorem sum_selectedKernelMean_eq_background (symbolic corrected mixed : Bool) :
    (∑p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      selectedKernelMean C p outside σ (J p) w P Q hactual hl houtside hw hpos hcell
        hlen hprime hV v f g symbolic corrected mixed) =
      (backgroundPrior C l).cmean (fun bg=>(selectedBulkPrior C l).cmean (fun u=>
        patternComplexSum C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
          (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
          (fun p b=>selectedKernelOptionValue C p outside σ (J p) w P Q hactual hl houtside hw hpos hcell
            hlen hprime hV v f g (restoreOuterBackground C l p bg b) symbolic corrected mixed u))) := by
  simp_rw [selectedKernelMean_eq_outerOption]
  exact typed_kernel_fubini C
    (fun p o u=>selectedKernelOptionValue C p outside σ (J p) w P Q hactual hl houtside hw hpos hcell
      hlen hprime hV v f g o symbolic corrected mixed u)
    (fun p o u=>selectedKernelOptionValue_typed C p outside σ (J p) w P Q hactual hl houtside hw hpos hcell
      hlen hprime hV v f g o symbolic corrected mixed u)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage

end

end OAI
