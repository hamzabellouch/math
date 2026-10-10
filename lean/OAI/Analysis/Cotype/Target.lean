import OAI.Analysis.Cotype.Cube

namespace OAI

noncomputable section
open scoped BigOperators
universe u
namespace Cotype

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

def FixedCotypeBound (m : ℕ) (D : ℝ) : Prop := 0 ≤ D ∧
  ∀ x : Fin m → E,
    Real.sqrt (∑ i, ‖x i‖ ^ 2) ≤ D * cubeL2 E (rademacherSum E x)

def ForwardTarget [CompleteSpace E] [Nontrivial E] : Prop :=
  KConvex E → FiniteCotype E ∧ FiniteCotype (E →L[ℝ] ℝ)

end Cotype

end

end OAI
