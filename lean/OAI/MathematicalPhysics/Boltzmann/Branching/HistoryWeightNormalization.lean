import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceCollisionGeometry

namespace OAI

/-! # Exact survival-factor conversion for finite branching histories -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.ReferenceGeometry

/-- The potential changes Markov survival at rate λ into the original loss survival at rate ν. -/
theorem history_survival_normalization (a b : ℝ) {rate loss : ℝ → ℝ}
    (hrate : IntervalIntegrable rate volume a b) (hloss : IntervalIntegrable loss volume a b) :
    Real.exp (∫ s in a..b, rate s-loss s)*Real.exp (-(∫ s in a..b, rate s)) =
      Real.exp (-(∫ s in a..b, loss s)) := by
  rw [← Real.exp_add,intervalIntegral.integral_sub hrate hloss]
  congr 1
  ring

/-- Splitting a survival interval at collision times multiplies the survival factors. -/
theorem history_survival_split {a b c : ℝ} {loss : ℝ → ℝ}
    (hab : IntervalIntegrable loss volume a b) (hbc : IntervalIntegrable loss volume b c) :
    Real.exp (-(∫ s in a..b, loss s))*Real.exp (-(∫ s in b..c, loss s)) =
      Real.exp (-(∫ s in a..c, loss s)) := by
  rw [← Real.exp_add,← neg_add,intervalIntegral.integral_add_adjacent_intervals hab hbc]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
