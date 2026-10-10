import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelStageKernelValue
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelStageOptionSum
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelStagePair

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkActualPrincipalKernelStage
open HistoryBulkPrincipalCollisionError HistoryBulkActualGoodPrincipal
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
  (bg : Background C l)

theorem kernelValueCollisionRawProof
    (corrected mixed : Bool)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample
      (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
        Internal (Template.initial (2*(bulkSize k L/2)) k) l) C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    let outer := restoreOuterBackground C l p bg b
    let option := fun index : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) =>
      selectMatchedOuterReference (l:=l) (α:=α) C p outer outside σ (J bg) w P Q index
        hactual hl houtside hw hpos
    kernelBlockTrueValue C outside σ J w P Q hactual hl houtside hw hpos hcell hlen hp hV bg corrected mixed p b =
      ∑ index, (option index).elim 0 (fun matched =>
        referenceKernel (l:=l) (p:=p)
          (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
            Internal (Template.initial (2*(bulkSize k L/2)) k) l)
          C (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
          (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
          outside (outerNonbulk C l p outer)
          (matched.collisionReference (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k)
            (l:=l) (E:=E) (C:=C) (p:=p) (o:=outer) (outside:=outside) (σ:=σ) (J:=J bg)
            (α:=α) (w:=w) (P:=P) (Q:=Q) (i:=index) hcell hlen hp hV)
          (outerBlocks C l p outer) mixed * (selectedBulkPrior C l).cmean (fun sample =>
            (density (l:=l) (C:=C) (outside:=outside)
              (matched.frame (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l)
                (E:=E) (C:=C) (p:=p) (o:=outer) (outside:=outside) (σ:=σ) (J:=J bg)
                (α:=α) (w:=w) (P:=P) (Q:=Q) (i:=index) hcell hp) mixed : ℂ) *
              @ite ℂ ((true : Bool) ∧ ¬fibreSmallOutsideGuard (l:=l) C outside
                (outerNonbulk C l p outer) sample) (Classical.propDecidable _) 0
                ((matched.collisionReference (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
                    (k:=k) (l:=l) (E:=E) (C:=C) (p:=p) (o:=outer) (outside:=outside)
                    (σ:=σ) (J:=J bg) (α:=α) (w:=w) (P:=P) (Q:=Q) (i:=index) hcell hlen hp hV).value
                  (l:=l) (C:=C) (outside:=outside) (a:=outerNonbulk C l p outer)
                  (τ:=pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l) (p:=p)
                  (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
                    Internal (Template.initial (2*(bulkSize k L/2)) k) l)
                  corrected mixed sample))) :=
  @Eq.trans ℂ _ _ _
    (kernelBlockTrueValue_eq_raw C outside σ J w P Q hactual hl houtside hw hpos hcell hlen hp hV bg corrected mixed p b)
    (Eq.trans
      (selectedKernelOptionValue_cmean_sum_eq_kernelTermSum C outside σ J w P Q
        hactual hl houtside hw hpos hcell hlen hp hV bg corrected mixed p b)
      (selectedKernelOptionSum_eq_collisionOptionSum C outside σ J w P Q
        hactual hl houtside hw hpos hcell hlen hp hV bg p b corrected mixed))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
