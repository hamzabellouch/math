import Mathlib
import OAI.Combinatorics.KMedian.Process.HeavyActions

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch
variable {I : Type} [LinearOrder I] [Fintype I]

def enumeration (Full : Actions I I) (H : Finset I) :
    Fin (Fintype.card (HeavyAction Full H)) ≃ HeavyAction Full H := by
  letI : LinearOrder (I × I) :=
    LinearOrder.lift' (fun p : I × I => toLex p) (fun _ _ h => h)
  letI : LinearOrder (HeavyAction Full H) :=
    LinearOrder.lift' (fun e : HeavyAction Full H => toLex e) (fun _ _ h => h)
  exact (Fintype.orderIsoFinOfCardEq (HeavyAction Full H) rfl).toEquiv

theorem action_card (Full : Actions I I) (H : Finset I) :
    Fintype.card (HeavyAction Full H) ≤ Fintype.card I+(Fintype.card I)^2 := by
  change Fintype.card ({h : I // h ∉ H} ⊕ {p : I × I // p.1 ∈ H ∧ p.2 ∈ Full.erase p.1}) ≤ _
  rw [Fintype.card_sum]
  have h1 : Fintype.card {h : I // h ∉ H} ≤ Fintype.card I := Fintype.card_subtype_le _
  have h2 : Fintype.card {p : I × I // p.1 ∈ H ∧ p.2 ∈ Full.erase p.1} ≤ (Fintype.card I)^2 := by
    have hh := Fintype.card_subtype_le (fun p : I × I => p.1 ∈ H ∧ p.2 ∈ Full.erase p.1)
    simpa only [Fintype.card_prod,pow_two] using hh
  exact Nat.add_le_add h1 h2

end MetricKMedian.RationalBatchData
end
end

end OAI
