import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelCollision

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkPrincipalCollisionError HistoryBulkActualGoodPrincipal
attribute [local instance] Classical.propDecidable
attribute [local instance] HistoryBulkActualPrincipalBlockFamily.kernelStageValueInternalDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ}
  {σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))}
  {J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ}
  {α : Type} [Fintype α] {w : α→ℝ} {P Q : α→ℤ}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}
variable
  (hcell : ∀v,w v≠0 → 0<P v ∧ 0<Q v ∧
    |Real.log (P v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q v:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem kernelOption_symbolic_eq_collisionIntegrand
    (opt : Option (MatchedSelectedOuter C p o outside σ J w P Q i))
    (corrected mixed : Bool) (u : SelectedBulkSample C l) :
    @Option.elim (MatchedSelectedOuter C p o outside σ J w P Q i) ℂ opt (0:ℂ) (fun (R : MatchedSelectedOuter C p o outside σ J w P Q i)=>R.kernelTerm (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) (C:=C) (p:=p) (o:=o) (outside:=outside) (σ:=σ) (J:=J) (α:=α) (w:=w) (P:=P) (Q:=Q) (i:=i) hcell hlen hp hV true corrected mixed u) =
    @Option.elim (MatchedSelectedOuter C p o outside σ J w P Q i) ℂ opt (0:ℂ) (fun (R : MatchedSelectedOuter C p o outside σ J w P Q i)=>
      referenceKernel (l:=l) (p:=p)
        (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
          Internal (Template.initial (2*(bulkSize k L/2)) k) l)
        C (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
        outside (outerNonbulk C l p o) (R.collisionReference (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) (C:=C) (p:=p) (o:=o) (outside:=outside) (σ:=σ) (J:=J) (α:=α) (w:=w) (P:=P) (Q:=Q) (i:=i) hcell hlen hp hV)
        (outerBlocks C l p o) mixed *
      ((density (l:=l) (C:=C) (outside:=outside) (R.frame (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) (C:=C) (p:=p) (o:=o) (outside:=outside) (σ:=σ) (J:=J) (α:=α) (w:=w) (P:=P) (Q:=Q) (i:=i) hcell hp) mixed:ℂ) *
        @ite ℂ (¬fibreSmallOutsideGuard (l:=l) C outside (outerNonbulk C l p o) u)
          (Classical.propDecidable _) 0
          ((R.collisionReference (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) (C:=C) (p:=p) (o:=o) (outside:=outside) (σ:=σ) (J:=J) (α:=α) (w:=w) (P:=P) (Q:=Q) (i:=i) hcell hlen hp hV).value (l:=l) (C:=C) (outside:=outside) (a:=outerNonbulk C l p o)
            (τ:=pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l) (p:=p)
            (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
              Internal (Template.initial (2*(bulkSize k L/2)) k) l)
            corrected mixed u))) := by
  cases opt with
  | none => rfl
  | some R =>
    exact R.kernelTerm_symbolic_eq_collisionIntegrand
      (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
      (C:=C) (p:=p) (o:=o) (outside:=outside)
      (σ:=σ) (J:=J) (α:=α) (w:=w) (P:=P) (Q:=Q) (i:=i)
      hcell hlen hp hV corrected mixed u

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
