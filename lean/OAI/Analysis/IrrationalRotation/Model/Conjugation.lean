import OAI.Analysis.IrrationalRotation.Model.Commutant

namespace OAI

namespace Invariant233
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def IsConjugation (C : H → H) : Prop :=
  Function.Involutive C ∧ (∀ x y, C (x + y) = C x + C y) ∧
    (∀ (c : ℂ) x, C (c • x) = star c • C x) ∧ (∀ x, ‖C x‖ = ‖x‖)

end Invariant233

end OAI
