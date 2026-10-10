import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BalancedFluid
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BalancedCoefficientEvaluation

namespace OAI

/-! The compact balanced main theorem includes a terminating evaluator
for every mixed derivative of the prescribed force. -/

noncomputable section
namespace ForcedComputation.Balanced
open ShearFlows Set
open scoped ContDiff

/-- The two finite coefficients prescribe the compact zero-data flow for
every viscosity; named finite queries evaluate every force derivative. -/
theorem balanced_three_stack_realization :
    IsCompact BalancedVelocity.support ∧
    ∀ (I : Alternating.MachineInput) (hI : Alternating.ValidInput I),
      (∀ ν : ℝ, force I hI ν = BalancedVelocity.force₀ I hI +
        ν • BalancedVelocity.force₁ I hI) ∧
      (∀ (α : List (Fin 4)) (b : ℕ → RationalSpaceTime) (y : SpaceTime),
        IsFastName b y → ∀ (ε : ℚ) (hε : 0 < ε),
          ‖mixedDerivative (BalancedVelocity.force₀ I hI) α y -
            rationalVector (BalancedExpressions.evaluateCoefficient₀ I hI α b ε hε)‖ ≤ (ε : ℝ) ∧
          ‖mixedDerivative (BalancedVelocity.force₁ I hI) α y -
            rationalVector (BalancedExpressions.evaluateCoefficient₁ I hI α b ε hε)‖ ≤ (ε : ℝ)) ∧
      (∀ ν : ℝ, 0 < ν → FluidProperties I hI ν) ∧
      (∀ (ν : ℝ) (a : ℕ → ℚ), IsFastRealName a ν →
        ∀ (α : List (Fin 4)) (b : ℕ → RationalSpaceTime) (y : SpaceTime),
          IsFastName b y → ∀ (ε : ℚ) (hε : 0 < ε),
            ‖mixedDerivative (force I hI ν) α y -
              rationalVector (BalancedExpressions.evaluate I hI α a b ε hε)‖ ≤ (ε : ℝ)) ∧
      (∀ (ν : ℝ) (a : ℕ → ℚ), IsFastRealName a ν →
        ∀ (α : List (Fin 4)) (u v M : ℚ) (y : SpaceTime),
          y.1 ∈ Ioo (u : ℝ) v →
          (∀ j, |timeSpaceCoord j y| ≤ |(M : ℝ)|) →
          ‖mixedDerivative (force I hI ν) α y‖ ≤
            (BalancedExpressions.boxForceBound I hI α u v M a : ℝ)) := by
  refine ⟨BalancedVelocity.support_compact,?_⟩
  intro I hI
  refine ⟨BalancedVelocity.force_affine I hI,?_,
    fun ν hν => fluid_properties I hI hν,?_,?_⟩
  · intro α b y hb ε hε
    exact ⟨BalancedExpressions.evaluateCoefficient₀_spec I hI α hb ε hε,
      BalancedExpressions.evaluateCoefficient₁_spec I hI α hb ε hε⟩
  · intro ν a ha α b y hb ε hε
    exact BalancedExpressions.evaluate_spec I hI α ha hb ε hε
  · intro ν a ha α u v M y ht hy
    exact BalancedExpressions.boxForceBound_spec I hI α u v M ha y ht hy

end ForcedComputation.Balanced

end

end OAI
