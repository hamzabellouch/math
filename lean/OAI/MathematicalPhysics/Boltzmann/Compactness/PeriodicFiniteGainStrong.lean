import OAI.MathematicalPhysics.Boltzmann.Approximation.MassNormalizedCollisionLimits
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedGainCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedGainSmoothingAE
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedGainCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicStrongAverages
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicJointBudgetLimit

namespace OAI

section

/-! # Strong local convergence of convolutions of the actual localized physical gains -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness

theorem GlobalCollisionLimit.localized_gain_smoothing_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (R : ℝ) (η χ : C(Velocity,ℝ))
    (hη : HasCompactSupport η) (hχ : HasCompactSupport χ) :
    Tendsto (fun n => eLpNorm (fun p : (ℝ × Position) × Velocity =>
      (∫ u : Velocity, χ (p.2-u)*localizedPhysicalGain η
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (p.1,u))-
      (∫ u : Velocity, χ (p.2-u)*localizedPhysicalGain η G.weakLimit.kineticProfile (p.1,u)))
      1 (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let ν : Measure Velocity := volume.restrict (Metric.closedBall 0 R)
  let : IsFiniteMeasure ν :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne
  have hwi : Integrable (weightedNormalizedPair G.weakLimit.kineticProfile)
      (μ.prod (volume : Measure (Velocity × Velocity))) := by
    simpa only [Measure.volume_eq_prod] using weightedNormalizedPair_integrable
      G.weakLimit.kineticProfile_measurable (fun _ => G.weakLimit.nonnegative _)
      (G.weakLimit.kinetic_entropy_on_window hf hi hT)
  have he := localizedPhysicalGain_smoothing_ae η χ hη hχ
    G.weakLimit.kineticProfile_measurable hwi
  have hen n : ∀ᵐ x ∂μ, ∀ v : Velocity,
      (∫ u : Velocity, χ (v-u)*localizedPhysicalGain η
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (x,u)) =
      ∫ y : Velocity × Velocity, smoothedAngularKernel η χ (v,y)*normalizedPair volume
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (x,y) := by
    apply localizedPhysicalGain_smoothing_ae η χ hη hχ
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
    simpa only [Measure.volume_eq_prod] using weightedNormalizedPair_integrable
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
      (fun _ => (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _)
      ((approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integrable
        (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _))
  have hnorm n : eLpNorm (fun p : (ℝ × Position) × Velocity =>
      (∫ u : Velocity, χ (p.2-u)*localizedPhysicalGain η
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (p.1,u))-
      (∫ u : Velocity, χ (p.2-u)*localizedPhysicalGain η G.weakLimit.kineticProfile (p.1,u)))
        1 (μ.prod ν) =
      eLpNorm (fun p : (ℝ × Position) × Velocity =>
        (∫ y : Velocity × Velocity, smoothedAngularKernel η χ (p.2,y)*normalizedPair volume
          (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (p.1,y))-
        (∫ y : Velocity × Velocity, smoothedAngularKernel η χ (p.2,y)*
          normalizedPair volume G.weakLimit.kineticProfile (p.1,y))) 1 (μ.prod ν) := by
    apply eLpNorm_congr_ae
    have hh : ∀ᵐ x ∂μ, ∀ v : Velocity,
        (∫ u : Velocity, χ (v-u)*localizedPhysicalGain η
          (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (x,u))-
        (∫ u : Velocity, χ (v-u)*localizedPhysicalGain η G.weakLimit.kineticProfile (x,u)) =
        (∫ y : Velocity × Velocity, smoothedAngularKernel η χ (v,y)*normalizedPair volume
          (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (x,y))-
        (∫ y : Velocity × Velocity, smoothedAngularKernel η χ (v,y)*
          normalizedPair volume G.weakLimit.kineticProfile (x,y)) := by
      filter_upwards [hen n,he] with x hx hy
      exact fun v => congrArg₂ (fun a b : ℝ => a-b) (hx v) (hy v)
    exact (Measure.quasiMeasurePreserving_fst.ae hh).mono (fun p hp => hp p.2)
  have hc := G.smoothed_angular_average_strong hf hi hT R η χ hη hχ
  exact hc.congr' (Filter.Eventually.of_forall (fun n => (hnorm n).symm))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong convergence of the actual unsmoothed localized collision gains -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness CollisionCompactness.DoubleGain

theorem GlobalCollisionLimit.localized_gain_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (R : ℝ) (η : C(Velocity,ℝ)) (hη : HasCompactSupport η) :
    Tendsto (fun n => eLpNorm (fun p : (ℝ × Position) × Velocity =>
      localizedPhysicalGain η
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile p-
      localizedPhysicalGain η G.weakLimit.kineticProfile p)
      1 (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let F n := (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile
  let g := G.weakLimit.kineticProfile
  have hFm n : Measurable (F n) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
  have hFn n p : 0 ≤ F n p :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _
  have hEi n : Integrable (entropyGauge (F n)) (μ.prod volume) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integrable
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  have hEb n : (∫ p, entropyGauge (F n) p ∂μ.prod volume) ≤
      (volume.restrict (Icc 0 T)).real univ*approximationEntropyBudget f :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integral_le
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  apply localizedGain_strong_of_smoothing hFm hFn hEi hEb
    G.weakLimit.kineticProfile_measurable (fun _ => G.weakLimit.nonnegative _)
    (G.weakLimit.kinetic_entropy_on_window hf hi hT) η hη
    (Measure.prod_mono le_rfl Measure.restrict_le_self)
  intro χ hχ
  have hc := G.localized_gain_smoothing_strong hf hi hT R η χ hη hχ
  change Tendsto (fun n => eLpNorm (fun p =>
    velocitySmooth χ (localizedPhysicalGain η (F n)) p-
      velocitySmooth χ (localizedPhysicalGain η g) p) 1 _) atTop (𝓝 0)
  simpa only [velocitySmooth_eq_outgoing_convolution,F,g,μ] using hc

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong convergence of the full physical mass-normalized collision gains -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness CollisionCompactness.DoubleGain

theorem GlobalCollisionLimit.normalized_gain_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (R : ℝ) :
    Tendsto (fun n => eLpNorm (fun p : (ℝ × Position) × Velocity =>
      pairGain (normalizedPair volume
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile) p-
      pairGain (normalizedPair volume G.weakLimit.kineticProfile) p)
      1 (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let F n := (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile
  let g := G.weakLimit.kineticProfile
  have hFm n : Measurable (F n) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
  have hFn n p : 0 ≤ F n p :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _
  have hEi n : Integrable (entropyGauge (F n)) (μ.prod volume) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integrable
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  let C := max ((volume.restrict (Icc 0 T)).real univ*approximationEntropyBudget f)
    (∫ p, entropyGauge g p ∂μ.prod volume)
  have hEb n : (∫ p, entropyGauge (F n) p ∂μ.prod volume) ≤
      C := by
    apply le_trans _ (le_max_left _ _)
    exact (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integral_le
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  apply normalizedGain_strong_of_localized hFm hFn hEi hEb
    G.weakLimit.kineticProfile_measurable (fun _ => G.weakLimit.nonnegative _)
    (G.weakLimit.kinetic_entropy_on_window hf hi hT) (le_max_right _ _)
    (Measure.prod_mono le_rfl Measure.restrict_le_self)
  intro η hη
  exact G.localized_gain_strong hf hi hT R η hη

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong convergence of the actual finite mass-normalized gains -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness CollisionCompactness.DoubleGain

theorem GlobalCollisionLimit.finite_gain_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (R : ℝ) :
    Tendsto (fun n => eLpNorm (fun p : (ℝ × Position) × Velocity =>
      gain ((G.weakLimit.indices n:ℝ)+1)
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile p/
        (1+fiberMass volume (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile p.1)-
      gainDensity G.weakLimit.kineticProfile p/(1+fiberMass volume G.weakLimit.kineticProfile p.1))
      1 (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let F n := (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile
  let g := G.weakLimit.kineticProfile
  have hFm n : Measurable (F n) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
  have hFn n p : 0 ≤ F n p :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _
  have hEi n : Integrable (entropyGauge (F n)) (μ.prod volume) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integrable
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  let C := max ((volume.restrict (Icc 0 T)).real univ*approximationEntropyBudget f)
    (∫ p, entropyGauge g p ∂μ.prod volume)
  have hEb n : (∫ p, entropyGauge (F n) p ∂μ.prod volume) ≤
      C := by
    apply le_trans _ (le_max_left _ _)
    exact (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integral_le
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  let N (n : ℕ) : ℝ := (G.weakLimit.indices n:ℝ)+1
  have hN n : 0 < N n := by dsimp [N]; positivity
  have hNt : Tendsto N atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp G.weakLimit.increasing.tendsto_atTop).atTop_add tendsto_const_nhds
  obtain ⟨B,hB⟩ := (approximatingSolution_compactness_hypotheses f hfm hf hi
    (volume.restrict (Icc 0 T))).1.2
  have hFB n : eLpNorm (F n) 1 (μ.prod volume) ≤ B := hB (G.weakLimit.indices n)
  have hr := massRegularizedGain_L1 hFm hFn hEi hEb hN hNt B hFB
  let ν : Measure ((ℝ × Position) × Velocity) :=
    μ.prod ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))
  have hν : ν ≤ μ.prod volume := Measure.prod_mono le_rfl Measure.restrict_le_self
  have hrl : Tendsto (fun n => eLpNorm (fun p =>
      gain (N n) (F n) p/(1+fiberMass volume (F n) p.1)-
      gainDensity (F n) p/(1+fiberMass volume (F n) p.1)) 1 ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr (fun _ => zero_le)
      (fun _ => eLpNorm_mono_measure _ hν)
  have hp := G.normalized_gain_strong hf hi hT R
  have hp' : Tendsto (fun n => eLpNorm (fun p =>
      gainDensity (F n) p/(1+fiberMass volume (F n) p.1)-
      gainDensity g p/(1+fiberMass volume g p.1)) 1 ν) atTop (𝓝 0) := by
    simpa only [normalizedPair_gain] using hp
  have ht := hrl.add hp'
  simp only [zero_add] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  have he : (fun p => gain (N n) (F n) p/(1+fiberMass volume (F n) p.1)-
      gainDensity g p/(1+fiberMass volume g p.1)) =
      (fun p => gain (N n) (F n) p/(1+fiberMass volume (F n) p.1)-
        gainDensity (F n) p/(1+fiberMass volume (F n) p.1))+
      (fun p => gainDensity (F n) p/(1+fiberMass volume (F n) p.1)-
        gainDensity g p/(1+fiberMass volume g p.1)) := by
    funext p
    simp only [Pi.add_apply]
    ring
  change eLpNorm (fun p => gain (N n) (F n) p/(1+fiberMass volume (F n) p.1)-
    gainDensity g p/(1+fiberMass volume g p.1)) 1 ν ≤ _
  rw [he]
  exact eLpNorm_add_le (by norm_num)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
