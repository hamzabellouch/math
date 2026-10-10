import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernel
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelTerm
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionNormalForm
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageValue

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation HistoryBulkFibreOriginalReference
open HistoryBulkPrincipalCollisionError
open HistoryBulkActualPrincipalCollision HistoryCompensationRepresentativePatterns
open HistoryPairRepresentatives HistoryPairKernelReplacement HistoryPairReferenceSourceTransport
attribute [local instance] Classical.propDecidable kernelStageValueInternalDecidable
private theorem guarded_product_congr (p : Prop) {s t : Decidable p}
    {a b c d density : ℂ} (hab : a=b) (hcd : c=d) :
    a * (density * @ite ℂ p s 0 c) = b * (density * @ite ℂ p t 0 d) := by
  cases hab
  cases hcd
  exact congrArg (fun x : ℂ => a * (density * x))
    ((ite_eq_ite (h:=s) (h':=t) p (0:ℂ) c).2 trivial)

variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ}
  {σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))}
  {J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ}
  {α : Type} [Fintype α] {w : α→ℝ} {P Q : α→ℤ}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}
namespace MatchedSelectedOuter
variable (R : MatchedSelectedOuter C p o outside σ J w P Q i)
  (hcell : ∀v,w v≠0 → 0<P v ∧ 0<Q v ∧
    |Real.log (P v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q v:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem kernelTerm_symbolic_eq_collisionIntegrand (corrected mixed : Bool)
    (u : SelectedBulkSample C l) :
    R.kernelTerm (l:=l) hcell hlen hp hV true corrected mixed u =
      referenceKernel (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕ Internal (Template.initial (2*(bulkSize k L/2)) k) l) (l:=l) (p:=p) C
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
        outside (outerNonbulk C l p o) (R.collisionReference (l:=l) hcell hlen hp hV)
        (outerBlocks C l p o) mixed *
      ((HistoryBulkActualGoodPrincipal.density (l:=l) (R.frame (l:=l) hcell hp) mixed:ℂ) *
        (@ite ℂ (¬fibreSmallOutsideGuard (l:=l) C outside (outerNonbulk C l p o) u) (Classical.propDecidable _) 0
          ((R.collisionReference (l:=l) hcell hlen hp hV).value (l:=l) (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕ Internal (Template.initial (2*(bulkSize k L/2)) k) l) corrected mixed u))) := by
  have h0 := R.kernelTerm_eq_guarded_product (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) (C:=C) (p:=p) (o:=o) (outside:=outside) (σ:=σ) (J:=J) (α:=α) (w:=w) (P:=P) (Q:=Q) (i:=i) hcell hlen hp hV true corrected mixed u
  have h1 := R.kernelProduct_symbolic_eq_referenceKernel (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) (C:=C) (p:=p) (o:=o) (outside:=outside) (σ:=σ) (J:=J) (α:=α) (w:=w) (P:=P) (Q:=Q) (i:=i) hcell hlen hp hV mixed u
  have h2 := R.collisionReference_value (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) (C:=C) (p:=p) (o:=o) (outside:=outside) (σ:=σ) (J:=J) (α:=α) (w:=w) (P:=P) (Q:=Q) (i:=i) hcell hlen hp hV corrected mixed u
  apply Eq.trans (α:=ℂ) h0
  exact guarded_product_congr
    (¬fibreSmallOutsideGuard (l:=l) C outside (outerNonbulk C l p o) u) h1 h2.symm

end MatchedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
