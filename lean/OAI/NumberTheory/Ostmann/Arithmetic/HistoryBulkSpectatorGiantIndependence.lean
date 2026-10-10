import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorGiantIndependenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkTransportAssigned

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSpectatorGiantIndependence
open Construction HistorySignedSpectatorCRT HistoryPairBulkTransport

theorem assigned_pair_eq_fixed_giants (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ) (N l : ℕ)
    (s t : ℤ) (gp gm : ℕ)
    (x y : SourceAssignment sources (Template.current seed l))
    (c e : HistoryChoices sources seed V l) (z : ZMod N×ZMod N) :
    residuePairSpectator g outside N (assignedHistory sources seed V l s gp gm x c)
      (assignedHistory sources seed V l t gp gm y e) z =
    residuePairSpectator g outside N (assignedHistory sources seed V l s 1 1 x c)
      (assignedHistory sources seed V l t 1 1 y e) z := by
  apply residuePairSpectator_decode_eq <;> rfl

end Ostmann.Arithmetic.HistoryBulkSpectatorGiantIndependence

end

end OAI
