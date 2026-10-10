import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

namespace FiniteFactor
open Filter
open scoped Topology
universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A concrete factor has scalar center. -/
def HasScalarCenter (M : VonNeumannAlgebra H) : Prop :=
  ∀ a ∈ M, (∀ b ∈ M, a * b = b * a) → ∃ z : ℂ, a = z • (1 : H →L[ℂ] H)

/-- Finiteness: every isometry in the algebra is unitary. -/
def IsFiniteAlgebra (M : VonNeumannAlgebra H) : Prop :=
  ∀ v ∈ M, star v * v = 1 → v * star v = 1

/-- No nonzero projection is minimal, excluding matrix factors. -/
def HasNoMinimalProjection (M : VonNeumannAlgebra H) : Prop :=
  ∀ p ∈ M, IsStarProjection p → p ≠ 0 →
    ∃ q ∈ M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ q * p = q

/-- A separable Banach space whose dual is conjugate-linearly isometric to M. -/
def HasSeparablePredual (M : VonNeumannAlgebra H) : Prop :=
  ∃ (E : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E)
    (_ : CompleteSpace E) (_ : TopologicalSpace.SeparableSpace E),
    Nonempty (StrongDual ℂ E ≃ₗᵢ⋆[ℂ] M.toStarSubalgebra)

def MainTarget : Prop :=
  ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (M : VonNeumannAlgebra H),
    HasScalarCenter M ∧ IsFiniteAlgebra M ∧ HasNoMinimalProjection M ∧
    HasSeparablePredual M ∧
    ∃ T : H →L[ℂ] H, T ∈ M ∧ T ≠ 0 ∧
      Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0) ∧
      ∀ p ∈ M, IsStarProjection p → (1 - p) * T * p = 0 → p = 0 ∨ p = 1

theorem main_theorem : MainTarget.{0} := by
  sorry

end FiniteFactor

end OAI
