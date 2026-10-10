import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveComparisonBound
import OAI.MathematicalPhysics.Boltzmann.Approximation.RegularizedEntropyIntegrability

namespace OAI

/-! # Retaining dissipation in the Gaussian regularization estimate -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem regularized_entropy_dissipation_bound (hcarleman : Published.GPV2009CarlemanInput)
    {μ : Measure X} [IsFiniteMeasure μ] {q A δ b p : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hδ : 0 < δ) (hδone : δ ≤ 1) (hb : 0 ≤ b)
    (hp : 1 < p) (hpi : Integrable (fun v : Velocity => H q v^p))
    {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hfn : ∀ z, 0 ≤ f z) (hfb : ∀ z, f z ≤ A*H q z.2) :
    Integrable (positiveCutoffProduction b (gaussianRegularizedDensity δ f))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ∧
    (∫ z, Real.log (gaussianRegularizedDensity δ f z/maxwellian z.2)*collisionSource b f z
        ∂μ.prod volume) +
      (∫ z, positiveCutoffProduction b (gaussianRegularizedDensity δ f) z
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤
      (δ*entropyErrorCoefficient q A b)*∫ z : X × Velocity,
        logarithmicMajorant q (A+tiltConstant) p δ z.2 ∂μ.prod volume := by
  let u := gaussianRegularizedDensity δ f
  have hum : Measurable u := gaussianRegularizedDensity_measurable δ hfm
  have huB : ∀ z, u z ≤ (A+tiltConstant)*H q z.2 := fun z =>
    gaussianRegularization_bound hδ.le hδone (fun v => hfb (z.1,v)) z.2
  have huL : ∀ z, δ*Real.exp (-2*‖z.2‖^2) ≤ u z := by
    intro z
    dsimp [u,gaussianRegularizedDensity]
    linarith [hfn z]
  have hun : ∀ z, 0 ≤ u z := fun z => (mul_nonneg hδ.le (Real.exp_nonneg _)).trans (huL z)
  have hAB := add_nonneg hA tiltConstant_pos.le
  have hfi := bounded_log_source_integrable (μ := μ) hcarleman hq₁ hq₂ hA hAB hδ hb
    hfm hum hfn hfb huL huB
  have hui := bounded_log_source_integrable (μ := μ) hcarleman hq₁ hq₂ hAB hAB hδ hb
    hum hum hun huB huL huB
  have hidentity := bounded_positive_entropy_identity (μ := μ) hcarleman hq₁ hq₂ hAB hδ hb hum huL huB
  have hbnd := kinetic_log_integral_bound hq₂ hAB
    (mul_nonneg hδ.le (entropyErrorCoefficient_nonneg hA hb q)) hδ hp hpi huL huB
    (kinetic_regularization_error_bound (μ := μ) hcarleman hδ.le hδone hA hq₁ hq₂ hb hfm hfn hfb)
  have he : (∫ z, Real.log (u z/maxwellian z.2)*(collisionSource b u z-collisionSource b f z)
      ∂μ.prod volume) =
      (∫ z, Real.log (u z/maxwellian z.2)*collisionSource b u z ∂μ.prod volume)-
      (∫ z, Real.log (u z/maxwellian z.2)*collisionSource b f z ∂μ.prod volume) := by
    simp_rw [mul_sub]
    exact integral_sub hui hfi
  rw [he,hidentity.2] at hbnd
  refine ⟨hidentity.1,?_⟩
  linarith [neg_abs_le (-(∫ z, positiveCutoffProduction b u z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)-
      (∫ z, Real.log (u z/maxwellian z.2)*collisionSource b f z ∂μ.prod volume))]

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
