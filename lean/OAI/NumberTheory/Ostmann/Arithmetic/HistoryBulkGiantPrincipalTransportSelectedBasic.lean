import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportModulus
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceNewModuliBounds

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport
open Construction HistoryCRTIntegration HistoryBulkReferenceNewModuli HistoryPairBulkTransport

lemma selected_spectator_primes (spectator : PrimeSource) {n : ℕ}
    (ds : Fin n → spectator.Sample) : ∀q∈spectatorList spectator ds,q.Prime := by
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact spectator.prime (ds i).val (ds i).property

lemma assigned_newComparisonModulus_pos (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (s : ℤ) (gp gm : ℕ)
    (x : SourceAssignment sources (Template.current seed l))
    (c : HistoryChoices sources seed V l) (h k : History l)
    {outside : List ℕ} (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hout : ∀q∈outside,q.Prime) (K : ℕ) :
    0 < newComparisonModulus (assignedHistory sources seed V l s gp gm x c) h k outside K :=
  mul_pos (mul_pos (mul_pos (assigned_rootModulus_pos sources seed V l s gp gm x c)
    (outsideModulus_pos hout)) (frequencyModulus_pos h k hs ks (K+2)))
    (representativeModulus_pos h k hs ks)

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
