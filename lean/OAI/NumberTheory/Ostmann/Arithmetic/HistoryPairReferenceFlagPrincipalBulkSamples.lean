import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRawSamples
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagPrincipalBulk

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open CanonicalHistoryLeafBulk HistoryBulkSpectatorReferenceRaw HistoryBulkProducts
attribute [local instance] Classical.propDecidable
local instance principalBulkSamplesInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (y : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)

@[simp] theorem originalDrawAssignment_val
    (i : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length) :
    (originalDrawAssignment C l p y i).val=(y (.inr (.inl i))).val := rfl

theorem originalDrawAssignment_integer_value
    (i : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length) :
    ((originalDrawAssignment C l p y i).val:ℤ)=
      originalDrawValues (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k)
        l p y (.inr (.inl i)) := rfl

theorem originalDrawBulk_bulkSamples (u : Fin (2^l) × Fin (2*(bulkSize k L/2))) :
    (originalDrawBulk C l p y u).val=
      bulkSamples C.sources (2*(bulkSize k L/2)) k l (originalDrawAssignment C l p y) u.1 u.2 :=
  originalDrawBulk_val C l p y u

theorem sourceBulkUnits_originalDrawAssignment (N : ℕ) :
    sourceBulkUnits N C.sources (2*(bulkSize k L/2)) k l (originalDrawAssignment C l p y)=
      fun u=>Characters.Template.unitConvention ((originalDrawBulk C l p y u).val:ZMod N) := by
  funext u
  rw [sourceBulkUnits,← originalDrawBulk_bulkSamples C l p y u]

theorem sourceBulkUnits_originalDrawAssignment_coe (N : ℕ)
    (hc : Nat.Coprime (bulkProduct (assignedSlots C.sources
      (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)
      (originalDrawAssignment C l p y))) N)
    (u : Fin (2^l) × Fin (2*(bulkSize k L/2))) :
    (sourceBulkUnits N C.sources (2*(bulkSize k L/2)) k l
      (originalDrawAssignment C l p y) u:ZMod N)=(originalDrawBulk C l p y u).val := by
  rw [sourceBulkUnits_coe N C.sources (2*(bulkSize k L/2)) k l
    (originalDrawAssignment C l p y) hc u,← originalDrawBulk_bulkSamples C l p y u]

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
