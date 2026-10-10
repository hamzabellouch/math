import OAI.Probability.SwitchChain.TripleActualRowBound
import OAI.Probability.SwitchChain.PairGeneratorSquare

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable

theorem tripleGenerator_square {n : ℕ} {d : Fin n → ℕ}
    (f : StateSpace n d) (T : Finset (Fin n)) (hT : T.card = 3) :
    ⟪f, tripleGenerator n d T f⟫ ≤
      ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫ := by
  rw [real_inner_self_eq_norm_sq, tripleGenerator_apply]
  exact TripleActualRowBound.triple_square T hT f

end Problem315.PairResampling

end

end OAI
