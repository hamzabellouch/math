import Mathlib

namespace OAI

section
section
section
noncomputable section
namespace CannonUniformization
open Set Metric unitInterval

variable {X : Type*} [MetricSpace X]

def annulusFamily (o : X) (r R : ℝ) : Set (Set X) :=
  {A | ∃ u v : X, ∃ p : Path u v, A = range p ∧ dist u o ≤ r ∧ R ≤ dist v o}
end CannonUniformization

end
end
end
end

end OAI
