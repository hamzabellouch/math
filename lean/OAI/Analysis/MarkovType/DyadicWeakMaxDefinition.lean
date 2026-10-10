import OAI.Analysis.MarkovType.FiniteDyadicMartingale

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

def DyadicNormalizedWeakMax (a A : ℝ) : Prop :=
  ∀ (N : ℕ) (φ : DyadicAtom N → E), dyadicRoot φ = 0 →
    finiteMoment dyadicInputWeight a φ ≤ 1 →
    ∀ t : ℝ, 0 < t →
      (dyadicLaw N).prob (fun ω => ∃ j : ℕ, j ≤ N ∧ t < ‖dyadicProcess φ j ω‖) ≤
        A / t ^ (a / 2)

end MarkovSuperreflexivity

end

end OAI
