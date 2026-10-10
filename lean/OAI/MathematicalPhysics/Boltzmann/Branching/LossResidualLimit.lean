import OAI.MathematicalPhysics.Boltzmann.Approximation.MassNormalizedCollisionLimits
import OAI.MathematicalPhysics.Boltzmann.Branching.UnitNormalizedResidual
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalL1ApproximationLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongMassClip

namespace OAI

section

/-! # The finite physical loss defect has a common unit-normalized integrability bound -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem loss_le_physical_ae {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyGauge f) (μ.prod volume)) :
    ∀ᵐ p ∂μ.prod (volume : Measure Velocity), loss N f p ≤ lossDensity f p := by
  have hfi := integrable_of_entropyGauge hfm hf hi
  have hli := linearMoment_integrable hfm hf hi
  have hvi : Integrable (fun p => ‖p.2‖*f p) (μ.prod volume) := by
    convert hli.sub hfi using 1
    funext p
    dsimp only [linearMoment,Pi.sub_apply]
    ring
  have h0 := (Measure.quasiMeasurePreserving_fst (μ := μ)
    (ν := (volume : Measure Velocity))).ae hfi.prod_right_ae
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ)
    (ν := (volume : Measure Velocity))).ae hvi.prod_right_ae
  filter_upwards [h0,h1] with p hp0 hp1
  exact loss_le_physical hN hfm hf p hp0 hp1

theorem lossResidual_unit_uniformIntegrable_local
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} {R C : ℝ} (hR : 0 ≤ R)
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p) (hN : ∀ n, 0 < N n)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UniformIntegrable (fun n p => (lossDensity (f n) p-loss (N n) (f n) p)/(1+f n p)) 1
      (μ.prod ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))) := by
  apply uniformIntegrable_abs_le (physicalLoss_unit_uniformIntegrable_local hR hfm hf hi hb)
    (fun n => (((lossDensity_measurable (hfm n)).sub (loss_measurable (N n) (hfm n))).div
      (measurable_const.add (hfm n))).aestronglyMeasurable)
  intro n
  have hν : μ.prod ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)) ≤
      μ.prod (volume : Measure Velocity) := Measure.prod_mono le_rfl Measure.restrict_le_self
  filter_upwards [ae_mono hν (loss_le_physical_ae (hN n) (hfm n) (hf n) (hi n))] with p hp
  have hl := (loss_bounds (hN n) (hfm n) (hf n) p).1
  have hd : 0 < 1+f n p := by linarith [hf n p]
  change |(lossDensity (f n) p-loss (N n) (f n) p)/(1+f n p)| ≤ _
  rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr hp) hd.le)]
  exact div_le_div_of_nonneg_right (sub_le_self _ hl) hd.le

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The unit-normalized finite loss defect vanishes -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem lossResidual_L1
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {N : ℕ → ℝ} {C R : ℝ}
    (hR : 0 ≤ R) (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hf : ∀ n p, 0 ≤ f n p) (hg : ∀ p, 0 ≤ g p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (B : ℝ≥0) (hB : ∀ n, eLpNorm (f n) 1 (μ.prod volume) ≤ B)
    (hm : Tendsto (fun n => eLpNorm
      (fun x => fiberMass volume (f n) x-fiberMass volume g x) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun p =>
      (lossDensity (f n) p-loss (N n) (f n) p)/(1+f n p)) 1
      (μ.prod ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) atTop (𝓝 0) := by
  let ν : Measure Velocity := volume.restrict (Metric.closedBall 0 R)
  let : IsFiniteMeasure ν :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne
  have hrm n : Measurable (fiberMass volume (f n)) := fiberMass_measurable (hfm n)
  have hsm : Measurable (fiberMass volume g) := fiberMass_measurable hgm
  have hmt : Tendsto (fun n => eLpNorm (fun p : X × Velocity =>
      fiberMass volume (f n) p.1-fiberMass volume g p.1) 1 (μ.prod ν)) atTop (𝓝 0) :=
    strongL1_comp_fst (μ := μ) (ν := ν)
      (f := fun n x => fiberMass volume (f n) x-fiberMass volume g x)
      (fun n => (hrm n).sub hsm) hm
  have hr := massRegularizedLoss_L1 (μ := μ) (f := f) (N := N) (C := C)
    hfm hf hi hb hN hNt B hB
  have hres : Tendsto (fun n => eLpNorm (fun p =>
      (lossDensity (f n) p-loss (N n) (f n) p)/(1+fiberMass volume (f n) p.1))
      1 (μ.prod ν)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr (fun _ => zero_le)
    intro n
    dsimp only
    have he : (fun p => (lossDensity (f n) p-loss (N n) (f n) p)/
        (1+fiberMass volume (f n) p.1)) =
        (fun p => lossDensity (f n) p/(1+fiberMass volume (f n) p.1))-
        (fun p => loss (N n) (f n) p/(1+fiberMass volume (f n) p.1)) := by
      funext p
      exact sub_div _ _ _
    rw [he,eLpNorm_sub_comm]
    exact eLpNorm_mono_measure _ (Measure.prod_mono le_rfl Measure.restrict_le_self)
  exact unitNormalized_residual_L1 (μ := μ.prod ν)
    (e := fun n p => lossDensity (f n) p-loss (N n) (f n) p)
    (u := f) (r := fun n p => fiberMass volume (f n) p.1)
    (s := fun p => fiberMass volume g p.1)
    (fun n => (lossDensity_measurable (hfm n)).sub (loss_measurable (N n) (hfm n))) hfm
    (fun n => (hrm n).comp measurable_fst) hf
    (fun n p => integral_nonneg (fun v => hf n (p.1,v)))
    (fun p => integral_nonneg (fun v => hg (p.1,v))) hmt hres
    (lossResidual_unit_uniformIntegrable_local hR hfm hf hN hi hb)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
