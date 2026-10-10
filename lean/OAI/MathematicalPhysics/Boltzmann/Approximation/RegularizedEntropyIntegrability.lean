import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedEntropyProduction
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyIntegralBalance
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticEntropyErrorLimit

namespace OAI

section

/-! # The finite-approximation entropy-production inequality, with vanishing error -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem bounded_log_source_integrable (hcarleman : Published.GPV2009CarlemanInput)
    {μ : Measure X} [IsFiniteMeasure μ] {q A B δ b : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 < δ) (hb : 0 ≤ b)
    {f u : X × Velocity → ℝ} (hfm : Measurable f) (hum : Measurable u)
    (hfn : ∀ z, 0 ≤ f z) (hfb : ∀ z, f z ≤ A*H q z.2)
    (hul : ∀ z, δ*Real.exp (-2*‖z.2‖^2) ≤ u z) (hub : ∀ z, u z ≤ B*H q z.2) :
    Integrable (fun z => Real.log (u z/maxwellian z.2)*collisionSource b f z) (μ.prod volume) := by
  have hpair := bounded_pair_integrable (μ := μ) hq₂ hA hfm hfn hfb
  have ht := bounded_log_gainLoss_integrable (μ := μ) hcarleman hq₁ hq₂ hA hB hδ hb
    hfm hum hfn hfb hul hub
  have hl : Integrable (fun z => Real.log (u z/maxwellian z.2)*
      (f z*KineticCollisionNullSets.frequency b f z)) (μ.prod volume) := by
    apply ht.2.congr
    filter_upwards [cutoff_loss_ae_eq_frequency hfm hfn hpair b] with z hz
    rw [hz]
  convert ht.1.sub hl using 1
  funext z
  simp only [collisionSource,Pi.sub_apply]
  ring

theorem regularized_entropy_production_bound (hcarleman : Published.GPV2009CarlemanInput)
    {μ : Measure X} [IsFiniteMeasure μ] {q A δ b p : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hδ : 0 < δ) (hδone : δ ≤ 1) (hb : 0 ≤ b)
    (hp : 1 < p) (hpi : Integrable (fun v : Velocity => H q v^p))
    {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hfn : ∀ z, 0 ≤ f z) (hfb : ∀ z, f z ≤ A*H q z.2) :
    (∫ z, Real.log (gaussianRegularizedDensity δ f z/maxwellian z.2)*collisionSource b f z
        ∂μ.prod volume) ≤
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
  have hnonpos := bounded_positive_entropy_production (μ := μ) hcarleman hq₁ hq₂ hAB hδ hb hum huL huB
  have hbnd := kinetic_log_integral_bound hq₂ hAB
    (mul_nonneg hδ.le (entropyErrorCoefficient_nonneg hA hb q)) hδ hp hpi huL huB
    (kinetic_regularization_error_bound (μ := μ) hcarleman hδ.le hδone hA hq₁ hq₂ hb hfm hfn hfb)
  have he : (∫ z, Real.log (u z/maxwellian z.2)*(collisionSource b u z-collisionSource b f z)
      ∂μ.prod volume) =
      (∫ z, Real.log (u z/maxwellian z.2)*collisionSource b u z ∂μ.prod volume)-
      (∫ z, Real.log (u z/maxwellian z.2)*collisionSource b f z ∂μ.prod volume) := by
    simp_rw [mul_sub]
    exact integral_sub hui hfi
  rw [he] at hbnd
  linarith [neg_abs_le ((∫ z, Real.log (u z/maxwellian z.2)*collisionSource b u z ∂μ.prod volume)-
      (∫ z, Real.log (u z/maxwellian z.2)*collisionSource b f z ∂μ.prod volume))]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Finite relative entropy of a Gaussian-regularized bounded approximation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem regularized_relative_entropy_integrable {μ : Measure X} [IsFiniteMeasure μ]
    {q A δ : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hδ : 0 < δ) (hδone : δ ≤ 1)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hfb : ∀ z, f z ≤ A*H q z.2) :
    Integrable (fun z => scalarRelativeEntropy (maxwellian z.2) (gaussianRegularizedDensity δ f z))
      (μ.prod volume) := by
  let g := gaussianRegularizedDensity δ f
  have hgm : Measurable g := gaussianRegularizedDensity_measurable δ hfm
  have hgn : ∀ z, 0 ≤ g z := fun z => add_nonneg (hfn z) (mul_nonneg hδ.le (Real.exp_nonneg _))
  have hgb : ∀ z, g z ≤ (A+tiltConstant)*H q z.2 := fun z =>
    gaussianRegularization_bound hδ.le hδone (fun v => hfb (z.1,v)) z.2
  have hgl : ∀ z, δ*Real.exp (-2*‖z.2‖^2) ≤ g z := by
    intro z
    dsimp [g,gaussianRegularizedDensity]
    linarith [hfn z]
  have hgint : Integrable g (μ.prod (volume : Measure Velocity)) := by
    apply (((integrable_H hq₂).const_mul (A+tiltConstant)).comp_snd μ).mono' hgm.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (hgn z)]
    exact hgb z
  have hlog := kinetic_log_product_integrable (μ := μ) hq₁ hq₂
    (add_nonneg hA tiltConstant_pos.le) (add_nonneg hA tiltConstant_pos.le) hδ hgm hgm hgl hgb
    (Filter.Eventually.of_forall (fun z => by rw [abs_of_nonneg (hgn z)]; exact hgb z))
  have hM := integrable_maxwellian.comp_snd μ
  convert (hlog.sub hgint).add hM using 1
  funext z
  rw [scalarRelativeEntropy_eq (maxwellian_pos z.2)]
  simp only [Pi.add_apply,Pi.sub_apply,g]
  ring

end BoltzmannNonuniqueness

end

end

end OAI
