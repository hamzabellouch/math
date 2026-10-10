import OAI.Computability.LoopMatching.LiteralChoices
import OAI.Computability.LoopMatching.SmallBoundary
import OAI.Computability.LoopMatching.Main

namespace OAI

namespace LoopMatchingReference

theorem challenge :
    ∃ A : LoopMatching.Input → ℕ × ℕ,
      ∃ machine : Turing.TM2ComputableInPolyTime
          LoopMatching.encodeInput LoopMatching.encodeOutput A,
        (∀ k, Finite (machine.tm.Γ k)) ∧
        (∃ P : Polynomial ℕ, ∀ G,
          (LoopMatching.encodeOutput (A G)).length ≤
            P.eval (LoopMatching.encodeInput G).length) ∧
        ∀ G, 0 < (A G).2 ∧
          (A G).1 ≤ (A G).2 * LoopMatching.count G ∧
          (A G).2 * LoopMatching.count G ≤ 2 ^ (18 * G.n) * (A G).1 ∧
          ((A G).1 = 0 ↔ LoopMatching.count G = 0) := by
  exact LoopMatching.fullEndpoint

end LoopMatchingReference

end OAI
