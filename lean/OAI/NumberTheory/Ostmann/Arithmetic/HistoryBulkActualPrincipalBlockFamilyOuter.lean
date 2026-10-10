import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagPrincipalBulkSamples
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagPrincipalOuter

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkSourceDisintegration
open HistoryBulkFibreOriginalReference
attribute [local instance] Classical.propDecidable
local instance actualPrincipalOuterInternalDecidable (template : List SourceSlot) (l : ℕ) : DecidableEq (Internal template l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ)
variable (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))

def outerNonbulk (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p) :
    SelectedNonbulkSample C l :=
  fun i=>o ⟨.inr (.inl i.val),i.property⟩

def outerBlocks (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p) :
    Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l) :=
  fun q=>o ⟨.inr (.inr q),by simp only [originalIndexIsBulk,not_false_eq_true]⟩

def outerGiants (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p) : Bool → C.giant.Sample :=
  fun q=>o ⟨.inl q,by simp only [originalIndexIsBulk,not_false_eq_true]⟩

@[simp] theorem outerNonbulk_originalDrawOuter
    (y : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (i : NonbulkPosition (SelectedTemplate k L l)) :
    outerNonbulk C l p (originalDrawOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y) i =
      originalDrawAssignment C l p y i.val := rfl

@[simp] theorem outerBlocks_originalDrawOuter
    (y : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p) (q : Block p) :
    outerBlocks C l p (originalDrawOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y) q =
      y (.inr (.inr q)) := rfl

@[simp] theorem outerGiants_originalDrawOuter
    (y : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p) (q : Bool) :
    outerGiants C l p (originalDrawOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y) q =
      y (.inl q) := rfl

theorem originalDrawAssignment_selectedSourceEquiv
    (y : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p) :
    selectedSourceEquiv C l (originalDrawAssignment C l p y) =
      (outerNonbulk C l p (originalDrawOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y),
        originalDrawBulk C l p y) := by
  apply Prod.ext
  · rfl
  · funext u
    apply Subtype.ext
    rw [selectedSourceEquiv_bulk_val,originalDrawBulk_val]
    rfl

theorem originalDrawAssignment_eq_fibreAssignment
    (y : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p) :
    originalDrawAssignment C l p y =
      fibreAssignment C
        (outerNonbulk C l p (originalDrawOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y))
        (originalDrawBulk C l p y) := by
  unfold fibreAssignment
  rw [←originalDrawAssignment_selectedSourceEquiv C l p y,Equiv.symm_apply_apply]

end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
