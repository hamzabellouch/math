import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuter

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkSourceDisintegration
open HistoryBulkFibreOriginalReference
attribute [local instance] Classical.propDecidable
local instance originalOuterEquivInternalDecidable (template : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal template l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))

def restoreOriginalDraw
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (u : SelectedBulkSample C l) :
    OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p
  | .inl b => outerGiants C l p o b
  | .inr (.inl i) => fibreAssignment C (outerNonbulk C l p o) u i
  | .inr (.inr q) => outerBlocks C l p o q

@[simp] theorem originalDrawAssignment_restore
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (u : SelectedBulkSample C l) :
    originalDrawAssignment C l p (restoreOriginalDraw C l p o u)=
      fibreAssignment C (outerNonbulk C l p o) u := rfl

@[simp] theorem originalDrawOuter_restore
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (u : SelectedBulkSample C l) :
    originalDrawOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p
      (restoreOriginalDraw C l p o u)=o := by
  funext j
  rcases j with ⟨j,hj⟩
  rcases j with b | i | q
  · rfl
  · exact fibreAssignment_nonbulk C (outerNonbulk C l p o) u ⟨i,hj⟩
  · rfl

@[simp] theorem originalDrawBulk_restore
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (u : SelectedBulkSample C l) :
    originalDrawBulk C l p (restoreOriginalDraw C l p o u)=u := by
  have h := congrArg Prod.snd
    (originalDrawAssignment_selectedSourceEquiv C l p (restoreOriginalDraw C l p o u))
  rw [originalDrawAssignment_restore,fibreAssignment,Equiv.apply_symm_apply] at h
  exact h.symm

@[simp] theorem restoreOriginalDraw_projections
    (y : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p) :
    restoreOriginalDraw C l p
      (originalDrawOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y)
      (originalDrawBulk C l p y)=y := by
  funext j
  rcases j with b | i | q
  · rfl
  · exact congrFun (originalDrawAssignment_eq_fibreAssignment C l p y).symm i
  · rfl

def originalDrawOuterEquiv :
    OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p ≃
      OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p ×
        SelectedBulkSample C l where
  toFun y := (originalDrawOuter (fun _=>C.giant) C.sources
    (Template.initial (2*(bulkSize k L/2)) k) l p y,originalDrawBulk C l p y)
  invFun z := restoreOriginalDraw C l p z.1 z.2
  left_inv := restoreOriginalDraw_projections C l p
  right_inv z := by
    apply Prod.ext
    · exact originalDrawOuter_restore C l p z.1 z.2
    · exact originalDrawBulk_restore C l p z.1 z.2

end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
