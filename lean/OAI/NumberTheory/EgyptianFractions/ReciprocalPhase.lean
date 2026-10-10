import OAI.NumberTheory.EgyptianFractions.ReciprocalPhaseUniform
import OAI.NumberTheory.EgyptianFractions.ReciprocalTerminalSum

namespace OAI
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Problem337

/-- Uniform local power cancellation for reciprocal phases, with no analytic
hypotheses beyond the indicated numerator range. -/
theorem reciprocal_phase_local_power_saving (B : ℝ) (hB : 4 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧
      ∀ᶠ U : ℝ in atTop, ∀ (Z : ℝ) (L R : ℤ),
        U ^ (4 : ℕ) ≤ |Z| → |Z| ≤ U ^ B →
        U ≤ (L : ℝ) → (R : ℝ) ≤ 2 * U →
        ‖∑ n ∈ Finset.Icc L R, differencingPhase (Z / (n : ℝ))‖ ≤
          A * U ^ (1 - δ) := by
  exact reciprocal_phase_uniform_of_terminal reciprocal_terminal_bound_eventually B hB

end Problem337

end

end OAI
