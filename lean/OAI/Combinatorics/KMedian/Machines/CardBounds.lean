import Mathlib
import OAI.Combinatorics.KMedian.PCP.BinaryReduction

namespace OAI

section Inline_PCPCardBounds
namespace MetricKMedian.PCP.AlphabetReduction
open scoped Classical

variable {V E K : Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq K]
variable (C : BinaryCSP V E (BitVector K))
lemma binary_card_bounds_nat :
    Nat.card (Position C ⊕ Test (E := E) (K := K)) ≤
      Nat.card V*Nat.card (BitVector K)+Nat.card E*(interiorBound K+Nat.card (EdgeSample K)) ∧
    Nat.card (Test (E := E) (K := K) × Fin 4)=Nat.card E*(4*Nat.card (EdgeSample K)) := by
  simpa only [← Nat.card_eq_fintype_card] using binary_card_bounds C
end MetricKMedian.PCP.AlphabetReduction

end Inline_PCPCardBounds

end OAI
