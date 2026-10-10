import OAI.Analysis.IrrationalRotation.Model.Commutant
import OAI.Analysis.IrrationalRotation.Model.OperatorProperties
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace OAI

noncomputable section
namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def IsHyperfinite (M : VonNeumannAlgebra H) : Prop :=
  ∃ A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H), Monotone A ∧
    (∀ n, A n ≤ M.toStarSubalgebra) ∧
    (∀ n, FiniteDimensional ℂ (A n)) ∧
    closure {B : H →Lₚₜ[ℂ] H | ∃ n, strongOperatorUnderlying B ∈ A n} =
      {B : H →Lₚₜ[ℂ] H | strongOperatorUnderlying B ∈ M}

end Invariant233

end

end OAI
