import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalDensity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationCollisionGuard

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference
open HistoryBulkReferencePeriodicMeanSource HistoryBulkPrincipalCollisionError
open HistoryBulkFibreIntegralReplacementFrame HistoryBulkActualGoodPrincipal
open HistoryBulkIndependentFibreReference HistorySignedResidueFactorization
attribute [local instance] Classical.propDecidable

private theorem guard_product_reorder (g : Prop) (D z K : ℂ) :
    guardIndicator g * (D * (z*K))=K*(D*(if ¬g then 0 else z)) := by
  by_cases hg : g
  · simp only [guardIndicator,hg,not_true_eq_false,ite_true,ite_false,one_mul]
    exact (mul_assoc D z K).symm.trans (mul_comm (D*z) K)
  · simp only [guardIndicator,hg,not_false_eq_true,ite_true,ite_false,zero_mul,mul_zero]

variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}

theorem Frame.plain_guard_density_product (r : Frame (l:=l) C outside)
    (σ : Equiv.Perm (Frame.Slots (depth:=k) (L:=L) (l:=l)))
    (a : SelectedNonbulkSample C l) (u : SelectedBulkSample C l)
    (mixed : Bool) (z K : ℂ) :
    staticPairMask (r.newLeft (fibreAssignment C a u))
      (r.newRight (permuteAssignment C σ (fibreAssignment C a u))) outside *
      (rootDensity r mixed * (z*K))=
    K*((density r mixed:ℂ)*(if ¬fibreSmallOutsideGuard C outside a u then 0 else z)) := by
  rw [r.plain_staticPairMask_eq_fibreSmallOutsideGuard σ a u,density_cast]
  exact guard_product_reorder (fibreSmallOutsideGuard C outside a u) (rootDensity r mixed) z K

theorem Frame.corrected_guard_density_product (r : Frame (l:=l) C outside)
    (a : SelectedNonbulkSample C l)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (he : PreservesRemainingBands _ e) (u : SelectedBulkSample C l)
    (hc : Compatible C a e u) (mixed : Bool) (z K : ℂ) :
    staticPairMask (r.newLeft (fibreAssignment C a u))
      (r.newRight (rightAssignment C a e u hc)) outside *
      (rootDensity r mixed * (z*K))=
    K*((density r mixed:ℂ)*(if ¬fibreSmallOutsideGuard C outside a u then 0 else z)) := by
  rw [r.corrected_staticPairMask_eq_fibreSmallOutsideGuard a e he u hc,density_cast]
  exact guard_product_reorder (fibreSmallOutsideGuard C outside a u) (rootDensity r mixed) z K

end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

end

end OAI
