import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionFalseAlgebra
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelStageKernelValueMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionSelectedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionSelectedPattern
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryKernelBlock

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkPrincipalCollisionError HistoryBulkActualGoodPrincipal
open HistoryBulkActualPrincipalKernelStage HistoryBulkUniversalPatternAggregation
attribute [local instance] Classical.propDecidable
attribute [local instance] HistoryBulkActualPrincipalKernelStage.kernelStageOptionInternalDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (J : Background C l → Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
  (hw : ∀r,0≤w r) (hpos : ∀r,w r≠0 → 0<P r ∧ 0<Q r)
  (hcell : ∀r,w r≠0 → 0<P r ∧ 0<Q r ∧
    |Real.log (P r:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q r:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem sum_selectedKernelMean_eq_collisionPrincipal (corrected mixed : Bool) :
    (∑ i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
      ∑ p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
        selectedKernelMean (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) (α:=α) (spectator:=spectator) C p outside σ
          (fun o => J (outerGiants C l p o, outerNonbulk C l p o)) w P Q
          hactual hl houtside hw hpos hcell hlen hp hV i.1 i.2.1 i.2.2 true corrected mixed) =
      (backgroundPrior C l).cmean (fun bg =>
        selectedCollisionMean (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) (α:=α) (spectator:=spectator) C outside σ (J bg) w P Q hactual hl houtside hw hpos
          hcell hlen hp hV bg corrected mixed true) :=
  @Eq.trans ℂ _ _ _
    (@sum_selectedKernelMean_eq_background_kernelValue d Bs BD Bz L k l E C outside σ J α (inferInstance : Fintype α) w P Q spectator hactual hl houtside hw hpos hcell hlen hp hV corrected mixed)
    (FinitePrior.cmean_congr_support (α:=Background C l) (backgroundPrior C l) _ _
      (fun bg _ => @Eq.trans ℂ _ _ _
        (patternComplexSum_congr_pointwise
          (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
            Internal (Template.initial (2*(bulkSize k L/2)) k) l)
          C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
          (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l) _ _
          (fun p b =>
            (kernelValueCollisionRawProof C outside σ J w P Q hactual hl houtside hw hpos
              hcell hlen hp hV bg corrected mixed p b).trans
              (restoredCollisionRaw_eq_selectedCollisionBlockValue C outside σ J w P Q
                hactual hl houtside hw hpos hcell hlen hp hV bg corrected mixed p b)))
        (@Eq.symm ℂ _ _ (@selectedCollisionMean_eq_pattern d Bs BD Bz L k l E C outside σ (J bg) α (inferInstance : Fintype α) w P Q spectator hactual hl houtside hw hpos hcell hlen hp hV bg corrected mixed true))))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
