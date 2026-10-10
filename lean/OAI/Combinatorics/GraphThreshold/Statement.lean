import OAI.Combinatorics.GraphThreshold.Model

namespace OAI

noncomputable section

universe u

namespace LeanBlast.SecondKahnKalai

def SecondKahnKalaiStatement : Prop :=
  ∀ (n : ℕ) (V : Type u) [Fintype V] (H : SimpleGraph V),
    2 ≤ n → Fintype.card V ≤ n → 1 ≤ edgeCount H →
      SecondKahnKalaiBounds n H

end LeanBlast.SecondKahnKalai

end

end OAI
