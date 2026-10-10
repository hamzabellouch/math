import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationSource
import OAI.NumberTheory.Ostmann.Conclusion.BulkPositionShape
import OAI.NumberTheory.Ostmann.Construction.InitialSourceChoice

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceSourceTransport HistoryPairSourceLaws
attribute [local instance] Classical.propDecidable
local instance principalBulkInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

section
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ)

def originalDrawBulkIndex (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (u : Fin (2^l) × Fin (2*(bulkSize k L/2))) : TypedSourceIndex p :=
  .inr (.inl ((currentBulkPositionEquiv (2*(bulkSize k L/2)) k l).symm u).val)

theorem originalDrawBulk_source (u : Fin (2^l) × Fin (2*(bulkSize k L/2))) :
    templateRootSources C.sources (Template.initial (2*(bulkSize k L/2)) k) l
      ((currentBulkPositionEquiv (2*(bulkSize k L/2)) k l).symm u).val=C.bulk :=
  current_bulk_source (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card)
    (C.cells.compSource E C.deleted_card) ((currentBulkPositionEquiv (2*(bulkSize k L/2)) k l).symm u)

theorem originalDrawBulk_origin (u : Fin (2^l) × Fin (2*(bulkSize k L/2))) :
    ((Template.current (Template.initial (2*(bulkSize k L/2)) k) l).get
      ((currentBulkPositionEquiv (2*(bulkSize k L/2)) k l).symm u).val).origin=u.2.val :=
  currentBulkPositionEquiv_origin (2*(bulkSize k L/2)) k l u.1 u.2

theorem originalDrawBulk_position (u : Fin (2^l) × Fin (2*(bulkSize k L/2))) :
    ((currentBulkPositionEquiv (2*(bulkSize k L/2)) k l).symm u).val.val=
      u.1.val*(bulkLeafTemplate (2*(bulkSize k L/2)) k l).length+u.2.val :=
  currentBulkPositionEquiv_symm_val (2*(bulkSize k L/2)) k l u.1 u.2

variable (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (y : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)

def originalDrawAssignment :
    SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) :=
  fun i=>y (.inr (.inl i))

def originalDrawBulk (u : Fin (2^l) × Fin (2*(bulkSize k L/2))) : C.bulk.Sample :=
  sourceSampleEquiv (originalDrawBulk_source C l u)
    (originalDrawAssignment C l p y ((currentBulkPositionEquiv (2*(bulkSize k L/2)) k l).symm u).val)

@[simp] theorem originalDrawBulk_val (u : Fin (2^l) × Fin (2*(bulkSize k L/2))) :
    (originalDrawBulk C l p y u).val=
      (y (.inr (.inl ((currentBulkPositionEquiv (2*(bulkSize k L/2)) k l).symm u).val))).val :=
  sourceSampleEquiv_val (originalDrawBulk_source C l u) _

theorem originalDrawBulk_integer_value (u : Fin (2^l) × Fin (2*(bulkSize k L/2))) :
    ((originalDrawBulk C l p y u).val:ℤ)=
      originalDrawValues (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y
        (originalDrawBulkIndex l p u) := by
  rw [originalDrawBulk_val]
  rfl

theorem originalDrawBulk_nat_value (u : Fin (2^l) × Fin (2*(bulkSize k L/2))) :
    (originalDrawBulk C l p y u).val=
      (originalDrawValues (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y
        (originalDrawBulkIndex l p u)).toNat := by
  rw [← originalDrawBulk_integer_value C l p y u,Int.toNat_natCast]

theorem originalDrawBulk_mass (u : Fin (2^l) × Fin (2*(bulkSize k L/2))) :
    C.bulk.law.mass (originalDrawBulk C l p y u)=
      mixedWeight (fun _=>C.giant) (templateRootSources C.sources (Template.initial (2*(bulkSize k L/2)) k) l)
        C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l) p
        (originalDrawBulkIndex l p u) (y (originalDrawBulkIndex l p u)) :=
  sourceSampleEquiv_mass (originalDrawBulk_source C l u) _

end
end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
