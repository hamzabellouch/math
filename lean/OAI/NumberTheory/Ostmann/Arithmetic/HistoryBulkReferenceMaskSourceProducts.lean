import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceMaskBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkTransportAssigned

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceMask
open Construction HistoryCRTIntegration HistoryPairBulkTransport

theorem assigned_rootModulus_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (s t : ℤ) (gp gm : ℕ)
    (x y : SourceAssignment sources (Template.current seed l))
    (c e : HistoryChoices sources seed V l)
    (π : Equiv.Perm (Fin (Template.current seed l).length))
    (hnew : ∀i, (y i).val=(x (π i)).val) :
    rootModulus (assignedHistory sources seed V l t gp gm y e)=
      rootModulus (assignedHistory sources seed V l s gp gm x c) := by
  simp only [rootModulus,assignedHistory,decodeHistory_root,assignedRoot,
    assignedSlots,Template.sample,List.map_ofFn,List.prod_ofFn,Function.comp_def]
  exact Fintype.prod_equiv π _ _ hnew

end Ostmann.Arithmetic.HistoryBulkReferenceMask

end

end OAI
