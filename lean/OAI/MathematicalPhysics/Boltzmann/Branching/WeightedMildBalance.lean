import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTransport
import OAI.MathematicalPhysics.Boltzmann.Approximation.MildCurveContinuity

namespace OAI

/-! # Velocity-weighted balances of an integrable characteristic source -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TorusFlight

theorem velocity_weighted_profile_balance {μ : Measure ℝ} [IsFiniteMeasure μ]
    (a : Density) (R : ℝ × Phase → ℝ) (ψ : Velocity → ℝ)
    (hRm : Measurable (fun z : ℝ × Phase => ψ z.2.2*R z))
    (hRi : Integrable (fun z : ℝ × Phase => ψ z.2.2*R z) (μ.prod volume))
    (hai : Integrable (fun p : Phase => ψ p.2*a p)) (t : ℝ) :
    (∫ p : Phase, ψ p.2*eulerianProfile μ a R t p) =
      (∫ p : Phase, ψ p.2*a p)+
        ∫ s, if s ≤ t then ∫ p : Phase, ψ p.2*R (s,p) else 0 ∂μ := by
  let W : ℝ × Phase → ℝ := fun z => ψ z.2.2*R z
  have hp : ∀ p : Phase, ψ p.2*Published.timePrimitive μ R (t,p) =
      Published.timePrimitive μ W (t,p) := by
    intro p
    change ψ p.2*(∫ s, if s ≤ t then R (s,p) else 0 ∂μ) =
      ∫ s, if s ≤ t then ψ p.2*R (s,p) else 0 ∂μ
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with s
    split_ifs <;> simp
  calc
    _ = ∫ p : Phase, ψ p.2*characteristicProfile μ a R t p := by
      have h := integral_flight (fun p : Phase => ψ p.2*characteristicProfile μ a R t p) (-t)
      exact h
    _ = ∫ p : Phase, ψ p.2*a p+Published.timePrimitive μ W (t,p) := by
      congr 1
      funext p
      dsimp [characteristicProfile]
      rw [mul_add,hp]
    _ = (∫ p : Phase, ψ p.2*a p)+(∫ p, Published.timePrimitive μ W (t,p)) :=
      integral_add hai (timePrimitive_slice_integrable hRm hRi t)
    _ = _ := by rw [Published.integral_timePrimitive hRi]

end BoltzmannNonuniqueness.TorusFlight

end

end OAI
