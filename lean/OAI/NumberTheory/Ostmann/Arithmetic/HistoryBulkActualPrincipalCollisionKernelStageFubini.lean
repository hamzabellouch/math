import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelStageSum
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStagePattern

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
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

theorem sum_selectedKernelMean_eq_background_pattern (corrected mixed : Bool) :
    (∑ i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
      ∑ p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
        selectedKernelMean (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) (α:=α) (spectator:=spectator) C p outside σ
          (fun o => J (outerGiants C l p o, outerNonbulk C l p o)) w P Q
          hactual hl houtside hw hpos hcell hlen hp hV i.1 i.2.1 i.2.2 true corrected mixed) =
      (backgroundPrior C l).cmean (fun bg =>
        patternComplexSum
          (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
            Internal (Template.initial (2*(bulkSize k L/2)) k) l)
          C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
          (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
          (fun p b => ∑ i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
            (selectedBulkPrior C l).cmean (fun u =>
              selectedKernelOptionValue (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) (α:=α) (spectator:=spectator) C p outside σ
                (fun o => J (outerGiants C l p o, outerNonbulk C l p o)) w P Q
                hactual hl houtside hw hpos hcell hlen hp hV i.1 i.2.1 i.2.2
                (restoreOuterBackground C l p bg b) true corrected mixed u))) := by
  simp_rw [sum_selectedKernelMean_eq_background (l:=l) C outside σ
    (fun p o => J (outerGiants C l p o, outerNonbulk C l p o)) w P Q
    hactual hl houtside hw hpos hcell hlen hp hV]
  exact kernelStage_sum_cmean_pattern
    (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
      Internal (Template.initial (2*(bulkSize k L/2)) k) l)
    (κ:=Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
    (α:=SelectedBulkSample C l) (β:=Background C l)
    C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
    (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
    (backgroundPrior C l) (selectedBulkPrior C l)
    (fun i bg u p b => selectedKernelOptionValue (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) (α:=α) (spectator:=spectator) C p outside σ
      (fun o => J (outerGiants C l p o, outerNonbulk C l p o)) w P Q
      hactual hl houtside hw hpos hcell hlen hp hV i.1 i.2.1 i.2.2
      (restoreOuterBackground C l p bg b) true corrected mixed u)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
