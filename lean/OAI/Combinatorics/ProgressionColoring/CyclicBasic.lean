import Mathlib.Data.ZMod.Basic

namespace OAI

/-! The common nonzero-step cyclic avoidance predicate. Colors are generic so
the constructed Boolean coloring and finite-cardinality transfers use the same
definition without a color conversion. -/

universe uAlpha

namespace QuantitativeVanDerWaerden

def CyclicAvoids {N : ℕ} {α : Type uAlpha} (C : ZMod N → α) (k : ℕ) : Prop :=
  ∀ a d, d ≠ 0 → ¬ (∀ j < k, C (a + (j : ZMod N) * d) = C a)

end QuantitativeVanDerWaerden

end OAI
