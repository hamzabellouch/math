import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterBackgroundDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageOption

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkActualPrincipalKernelStage
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

def kernelBlockTrueValue
    (corrected mixed : Bool)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample
      (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
        Internal (Template.initial (2*(bulkSize k L/2)) k) l) C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) : ℂ :=
  (∑ i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
      FinitePrior.cmean (ι:=SelectedBulkSample C l) (selectedBulkPrior C l)
        (fun u : SelectedBulkSample C l =>
          selectedKernelOptionValue (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
            (α:=α) (spectator:=spectator) C p outside σ
            (fun o => J (outerGiants C l p o, outerNonbulk C l p o)) w P Q
            hactual hl houtside hw hpos hcell hlen hp hV i.1 i.2.1 i.2.2
            (restoreOuterBackground C l p bg b) true corrected mixed u))

private theorem kernelBlockTrueValue_eq_raw_proof
    (corrected mixed : Bool)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample
      (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
        Internal (Template.initial (2*(bulkSize k L/2)) k) l) C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    kernelBlockTrueValue C outside σ J w P Q hactual hl houtside hw hpos hcell hlen hp hV bg corrected mixed p b =
  (∑ i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
      FinitePrior.cmean (ι:=SelectedBulkSample C l) (selectedBulkPrior C l)
        (fun u : SelectedBulkSample C l =>
          selectedKernelOptionValue (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
            (α:=α) (spectator:=spectator) C p outside σ
            (fun o => J (outerGiants C l p o, outerNonbulk C l p o)) w P Q
            hactual hl houtside hw hpos hcell hlen hp hV i.1 i.2.1 i.2.2
            (restoreOuterBackground C l p bg b) true corrected mixed u)) :=
  rfl

theorem kernelBlockTrueValue_eq_raw
    (corrected mixed : Bool)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample
      (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
        Internal (Template.initial (2*(bulkSize k L/2)) k) l) C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    kernelBlockTrueValue C outside σ J w P Q hactual hl houtside hw hpos hcell hlen hp hV bg corrected mixed p b =
  (∑ i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
      FinitePrior.cmean (ι:=SelectedBulkSample C l) (selectedBulkPrior C l)
        (fun u : SelectedBulkSample C l =>
          selectedKernelOptionValue (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
            (α:=α) (spectator:=spectator) C p outside σ
            (fun o => J (outerGiants C l p o, outerNonbulk C l p o)) w P Q
            hactual hl houtside hw hpos hcell hlen hp hV i.1 i.2.1 i.2.2
            (restoreOuterBackground C l p bg b) true corrected mixed u)) :=
  kernelBlockTrueValue_eq_raw_proof C outside σ J w P Q hactual hl houtside hw hpos hcell hlen hp hV bg corrected mixed p b

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
