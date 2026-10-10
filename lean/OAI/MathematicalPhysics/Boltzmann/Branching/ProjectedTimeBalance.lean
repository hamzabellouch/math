import OAI.MathematicalPhysics.Boltzmann.Branching.TimeSourceCumulative
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakTimeBalance

namespace OAI

/-! # Integrating a phase-tested weak kinetic equation in time -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

theorem projected_cumulative_balance {a b : ℝ} (hab : a < b)
    {F : ℝ × Phase → ℝ} (hF : Integrable F (volume : Measure (ℝ × Phase)))
    {φ : Phase → ℝ} (hφ : Measurable φ) (hn : ∀ p, 0 ≤ φ p)
    {B : ℝ} (hB : ∀ p, |φ p| ≤ B)
    (μ ν : Measure (ℝ × Phase)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hw : ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ →
      tsupport θ ⊆ Ioo a b →
      (∫ z, (deriv θ z.1*φ z.2)*F z)+
        (∫ z, θ z.1*φ z.2 ∂μ)-(∫ z, θ z.1*φ z.2 ∂ν) = 0) :
    ∃ c : ℝ, ∀ᵐ t ∂volume, t ∈ Ioo a b →
      phaseProjection F φ t = c+cumulative (timeSource μ φ) t-cumulative (timeSource ν φ) t := by
  let _ := timeSource_finite μ hφ hn hB
  let _ := timeSource_finite ν hφ hn hB
  apply ae_cumulative_balance hab (phaseProjection_integrable hF hφ hB).locallyIntegrable
    (timeSource μ φ) (timeSource ν φ)
  intro θ hθ hc hs
  obtain ⟨C,hC⟩ := (hθ.continuous_deriv (by simp)).bounded_above_of_compact_support hc.deriv
  rw [phaseProjection_test_integral hF hφ hB (hθ.continuous_deriv (by simp)).measurable hC,
    timeSource_integral μ hφ hn hθ.continuous.measurable,
    timeSource_integral ν hφ hn hθ.continuous.measurable]
  exact hw θ hθ hc hs

end BoltzmannNonuniqueness.WeakTime

end

end OAI
