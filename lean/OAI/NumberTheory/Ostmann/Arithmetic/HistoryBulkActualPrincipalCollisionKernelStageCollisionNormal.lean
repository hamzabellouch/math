import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionSelectedNormalForm

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkPrincipalCollisionError HistoryBulkActualGoodPrincipal
attribute [local instance] Classical.propDecidable collisionSelectedFormInternalDecidable
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

def collisionBlockTrueNormal
    (corrected mixed : Bool)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample
      (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
        Internal (Template.initial (2*(bulkSize k L/2)) k) l) C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) : ℂ :=
  ∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
    @Option.elim
      (MatchedSelectedOuter (l:=l) C p (restoreOuterBackground C l p bg b)
        outside σ (J bg) w P Q i) ℂ
      (selectMatchedOuterReference C p (restoreOuterBackground C l p bg b)
        outside σ (J bg) w P Q i hactual hl houtside hw hpos) 0
      (fun R =>
        referenceKernel (l:=l)
          (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
            Internal (Template.initial (2*(bulkSize k L/2)) k) l) C
          (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
          (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
          outside bg.2 (R.collisionReference hcell hlen hp hV) b mixed *
        (selectedBulkPrior C l).cmean (fun u => (density (R.frame hcell hp) mixed:ℂ) *
          (if true ∧ ¬fibreSmallOutsideGuard C outside bg.2 u then 0 else
            (R.collisionReference hcell hlen hp hV).value corrected mixed u)))

private theorem collisionBlockTrueNormal_eq_raw_proof
    (corrected mixed : Bool)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample
      (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
        Internal (Template.initial (2*(bulkSize k L/2)) k) l) C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    collisionBlockTrueNormal C outside σ J w P Q hactual hl houtside hw hpos hcell hlen hp hV bg corrected mixed p b =
  ∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
    @Option.elim
      (MatchedSelectedOuter (l:=l) C p (restoreOuterBackground C l p bg b)
        outside σ (J bg) w P Q i) ℂ
      (selectMatchedOuterReference C p (restoreOuterBackground C l p bg b)
        outside σ (J bg) w P Q i hactual hl houtside hw hpos) 0
      (fun R =>
        referenceKernel (l:=l)
          (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
            Internal (Template.initial (2*(bulkSize k L/2)) k) l) C
          (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
          (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
          outside bg.2 (R.collisionReference hcell hlen hp hV) b mixed *
        (selectedBulkPrior C l).cmean (fun u => (density (R.frame hcell hp) mixed:ℂ) *
          (if true ∧ ¬fibreSmallOutsideGuard C outside bg.2 u then 0 else
            (R.collisionReference hcell hlen hp hV).value corrected mixed u))) := rfl

theorem collisionBlockTrueNormal_eq_raw
    (corrected mixed : Bool)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample
      (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
        Internal (Template.initial (2*(bulkSize k L/2)) k) l) C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    collisionBlockTrueNormal C outside σ J w P Q hactual hl houtside hw hpos hcell hlen hp hV bg corrected mixed p b =
  ∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
    @Option.elim
      (MatchedSelectedOuter (l:=l) C p (restoreOuterBackground C l p bg b)
        outside σ (J bg) w P Q i) ℂ
      (selectMatchedOuterReference C p (restoreOuterBackground C l p bg b)
        outside σ (J bg) w P Q i hactual hl houtside hw hpos) 0
      (fun R =>
        referenceKernel (l:=l)
          (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
            Internal (Template.initial (2*(bulkSize k L/2)) k) l) C
          (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
          (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
          outside bg.2 (R.collisionReference hcell hlen hp hV) b mixed *
        (selectedBulkPrior C l).cmean (fun u => (density (R.frame hcell hp) mixed:ℂ) *
          (if true ∧ ¬fibreSmallOutsideGuard C outside bg.2 u then 0 else
            (R.collisionReference hcell hlen hp hV).value corrected mixed u))) :=
  collisionBlockTrueNormal_eq_raw_proof C outside σ J w P Q hactual hl houtside hw hpos hcell hlen hp hV bg corrected mixed p b

private theorem selectedCollisionBlockValue_true_eq_normal_proof
    (corrected mixed : Bool)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample
      (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
        Internal (Template.initial (2*(bulkSize k L/2)) k) l) C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    selectedCollisionBlockValue (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
      (k:=k) (l:=l) (E:=E) (α:=α) (spectator:=spectator)
      C outside σ (J bg) w P Q hactual hl houtside hw hpos hcell hlen hp hV
      bg corrected mixed true p b =
    collisionBlockTrueNormal C outside σ J w P Q hactual hl houtside hw hpos hcell hlen hp hV bg corrected mixed p b := rfl

theorem selectedCollisionBlockValue_true_eq_normal
    (corrected mixed : Bool)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample
      (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
        Internal (Template.initial (2*(bulkSize k L/2)) k) l) C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    selectedCollisionBlockValue (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
      (k:=k) (l:=l) (E:=E) (α:=α) (spectator:=spectator)
      C outside σ (J bg) w P Q hactual hl houtside hw hpos hcell hlen hp hV
      bg corrected mixed true p b =
    collisionBlockTrueNormal C outside σ J w P Q hactual hl houtside hw hpos hcell hlen hp hV bg corrected mixed p b :=
  selectedCollisionBlockValue_true_eq_normal_proof C outside σ J w P Q hactual hl houtside hw hpos hcell hlen hp hV bg corrected mixed p b

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
