import OAI.MathematicalPhysics.Boltzmann.Approximation.RegularizedLogBounds
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyDissipationAverage

namespace OAI

section

/-! # Integrable entropy tests for bounded kinetic densities -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem kinetic_log_product_integrable {μ : Measure X} [IsFiniteMeasure μ]
    {q B C δ : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hB : 0 ≤ B) (hC : 0 ≤ C) (hδ : 0 < δ)
    {u a : X × Velocity → ℝ} (hum : Measurable u) (ham : Measurable a)
    (hl : ∀ p, δ*Real.exp (-2*‖p.2‖^2) ≤ u p)
    (hu : ∀ p, u p ≤ B*H q p.2)
    (ha : ∀ᵐ p ∂μ.prod (volume : Measure Velocity), |a p| ≤ C*H q p.2) :
    Integrable (fun p => Real.log (u p/maxwellian p.2)*a p) (μ.prod volume) := by
  obtain ⟨p,hp,hpi⟩ := exists_integrable_rpow_H hq₁ hq₂
  have hmaj := ((logarithmicMajorant_integrable (B := B) (δ := δ) hq₂ hpi).const_mul C).comp_snd μ
  have hMm : Measurable (fun p : X × Velocity => maxwellian p.2) := by
    unfold maxwellian
    fun_prop
  apply hmaj.mono' (((hum.div hMm).log).mul ham).aestronglyMeasurable
  filter_upwards [ha] with z hz
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_mul]
  calc
    _ ≤ |Real.log (u z/maxwellian z.2)| * (C*H q z.2) :=
      mul_le_mul_of_nonneg_left hz (abs_nonneg _)
    _ = C*(|Real.log (u z/maxwellian z.2)| * H q z.2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (logarithm_weight_bound hB hp hδ z.2 (hl z) (hu z)) hC

end BoltzmannNonuniqueness

end

end

section

/-! # A quantitative integral bound for the kinetic logarithmic test -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem kinetic_log_integral_bound {μ : Measure X} [IsFiniteMeasure μ]
    {q B C δ p : ℝ} (hq : q < 2) (hB : 0 ≤ B) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hp : 1 < p) (hpi : Integrable (fun v : Velocity => H q v^p))
    {u a : X × Velocity → ℝ}
    (hl : ∀ z, δ*Real.exp (-2*‖z.2‖^2) ≤ u z) (hu : ∀ z, u z ≤ B*H q z.2)
    (ha : ∀ᵐ z ∂μ.prod (volume : Measure Velocity), |a z| ≤ C*H q z.2) :
    |∫ z, Real.log (u z/maxwellian z.2)*a z ∂μ.prod volume| ≤
      C*∫ z : X × Velocity, logarithmicMajorant q B p δ z.2 ∂μ.prod volume := by
  have hi := ((logarithmicMajorant_integrable (B := B) (δ := δ) hq hpi).const_mul C).comp_snd μ
  have hb : ∀ᵐ z ∂μ.prod (volume : Measure Velocity),
      ‖Real.log (u z/maxwellian z.2)*a z‖ ≤ C*logarithmicMajorant q B p δ z.2 := by
    filter_upwards [ha] with z hz
    rw [Real.norm_eq_abs,abs_mul]
    calc
      _ ≤ |Real.log (u z/maxwellian z.2)| * (C*H q z.2) :=
        mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ = C*(|Real.log (u z/maxwellian z.2)| * H q z.2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (logarithm_weight_bound hB hp hδ z.2 (hl z) (hu z)) hC
  have h := norm_integral_le_of_norm_le hi hb
  simpa only [Real.norm_eq_abs,integral_const_mul] using h

end BoltzmannNonuniqueness

end

end

section

/-! # The Gaussian entropy error is integrable on a finite kinetic base -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

def gaussianRegularizedDensity (δ : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  f p+δ*Real.exp (-2*‖p.2‖^2)

theorem gaussianRegularizedDensity_measurable (δ : ℝ) {f : X × Velocity → ℝ}
    (hfm : Measurable f) : Measurable (gaussianRegularizedDensity δ f) := by
  unfold gaussianRegularizedDensity
  fun_prop

theorem kinetic_regularization_error_bound (hcarleman : Published.GPV2009CarlemanInput)
    {μ : Measure X} [SFinite μ] {δ A q b : ℝ}
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hA : 0 ≤ A)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hfb : ∀ p, f p ≤ A*H q p.2) :
    ∀ᵐ p ∂μ.prod (volume : Measure Velocity),
      |CollisionCompactness.collisionSource b (gaussianRegularizedDensity δ f) p-
        CollisionCompactness.collisionSource b f p| ≤
          (δ*entropyErrorCoefficient q A b)*H q p.2 := by
  have hgm := gaussianRegularizedDensity_measurable δ hfm
  have hsm := (CollisionCompactness.collisionSource_measurable hgm b).sub
    (CollisionCompactness.collisionSource_measurable hfm b)
  have hH : Measurable (fun p : X × Velocity => (δ*entropyErrorCoefficient q A b)*H q p.2) := by
    unfold H singularity transverse
    fun_prop
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hsm.abs hH)).mpr
  filter_upwards [] with x
  have hx := gaussianRegularization_collision_error hcarleman hδ hδone hA hq₁ hq₂ hb
    (hfm.comp (measurable_const.prodMk measurable_id)) (fun v => hfn (x,v)) (fun v => hfb (x,v))
  exact hx

theorem kinetic_regularization_entropy_integrable (hcarleman : Published.GPV2009CarlemanInput)
    {μ : Measure X} [IsFiniteMeasure μ] {δ A q b : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hA : 0 ≤ A)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hfb : ∀ p, f p ≤ A*H q p.2) :
    Integrable (fun p => Real.log (gaussianRegularizedDensity δ f p/maxwellian p.2)*
      (CollisionCompactness.collisionSource b (gaussianRegularizedDensity δ f) p-
        CollisionCompactness.collisionSource b f p)) (μ.prod volume) := by
  have hgm := gaussianRegularizedDensity_measurable δ hfm
  apply kinetic_log_product_integrable hq₁ hq₂ (add_nonneg hA tiltConstant_pos.le)
    (mul_nonneg hδ.le (entropyErrorCoefficient_nonneg hA hb q)) hδ hgm
    ((CollisionCompactness.collisionSource_measurable hgm b).sub
      (CollisionCompactness.collisionSource_measurable hfm b))
  · intro p
    dsimp [gaussianRegularizedDensity]
    linarith [hfn p]
  · intro p
    exact gaussianRegularization_bound hδ.le hδone (fun v => hfb (p.1,v)) p.2
  · exact kinetic_regularization_error_bound hcarleman hδ.le hδone hA hq₁ hq₂ hb hfm hfn hfb

end BoltzmannNonuniqueness

end

end

section

/-! # Vanishing of the entropy-error majorant after integrating the finite base -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem kinetic_entropy_error_tendsto (μ : Measure X) [SFinite μ]
    {q B p : ℝ} (C : ℝ) (hq : q < 2)
    (hp : Integrable (fun v : Velocity => H q v^p)) :
    Tendsto (fun δ : ℝ => δ*C*(∫ z : X × Velocity,
      logarithmicMajorant q B p δ z.2 ∂μ.prod volume)) (𝓝 0) (𝓝 0) := by
  have h := (tendsto_integrated_entropy_error (B := B) C hq hp).mul_const (μ.real Set.univ)
  convert h using 1
  · funext δ
    rw [integral_fun_snd,smul_eq_mul]
    ring
  · ring_nf

end BoltzmannNonuniqueness

end

end

end OAI
