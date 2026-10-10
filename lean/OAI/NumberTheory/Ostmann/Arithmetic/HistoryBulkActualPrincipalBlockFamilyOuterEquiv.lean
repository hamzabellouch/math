import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterEquivBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterMass

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkSourceDisintegration
open HistoryBulkFibreOriginalReference
attribute [local instance] Classical.propDecidable
local instance originalOuterFubiniInternalDecidable (template : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal template l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))

@[simp] theorem originalDrawOuterEquiv_symm_apply
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (u : SelectedBulkSample C l) :
    (originalDrawOuterEquiv C l p).symm (o,u)=restoreOriginalDraw C l p o u := rfl

theorem sum_originalDraw_eq_outer_bulk {A : Type*} [AddCommMonoid A]
    (F : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p → A) :
    (∑ y,F y)=∑ o,∑ u,F (restoreOriginalDraw C l p o u) := by
  simpa only [Fintype.sum_prod_type,originalDrawOuterEquiv_symm_apply] using ((originalDrawOuterEquiv C l p).symm.sum_comp F).symm

@[simp] theorem originalDrawMass_restore
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (u : SelectedBulkSample C l) :
    originalDrawMass (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p
      (restoreOriginalDraw C l p o u)=outerMass C l p o*(selectedBulkPrior C l).mass u := by
  simpa only [originalDrawOuter_restore,originalDrawBulk_restore] using
    originalDrawMass_eq_outerMass_mul_bulkMass C l p (restoreOriginalDraw C l p o u)

theorem original_weighted_sum_eq_outer_cmean
    (F : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p → ℂ) :
    (∑ y,(originalDrawMass (fun _=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p y:ℂ)*F y)=
      ∑ o,(outerMass C l p o:ℂ)*(selectedBulkPrior C l).cmean
        (fun u=>F (restoreOriginalDraw C l p o u)) := by
  rw [sum_originalDraw_eq_outer_bulk C l p]
  simp only [originalDrawMass_restore,FinitePrior.cmean,Complex.ofReal_mul,
    Finset.mul_sum,mul_assoc]

theorem original_weighted_sum_eq_outer_mean
    (F : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p → ℝ) :
    (∑ y,originalDrawMass (fun _=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p y*F y)=
      ∑ o,outerMass C l p o*(selectedBulkPrior C l).mean
        (fun u=>F (restoreOriginalDraw C l p o u)) := by
  rw [sum_originalDraw_eq_outer_bulk C l p]
  simp only [originalDrawMass_restore,FinitePrior.mean,Finset.mul_sum,mul_assoc]

end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
