import OAI.MathematicalPhysics.Boltzmann.Approximation.MassNormalizedCollisionLimits
import OAI.MathematicalPhysics.Boltzmann.Branching.GainMeasureLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.LossResidualLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalL1ApproximationLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicStrongAverages
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicJointBudgetLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.RenormalizedCollisionIntegrability
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusVelocityWindowAE

namespace OAI

section

/-! # The unit-normalized gain bound along every sufficiently late actual subsequence -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem approximatingSolution_subsequence_gain_unit_uniformIntegrable
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyMoment f)) {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (ι : ℕ → ℕ) (hι : ∀ n, Nat.ceil T ≤ ι n) :
    UniformIntegrable (fun n p =>
      gain ((ι n:ℝ)+1) (approximatingSolution f hfm (ι n)).kineticProfile p/
        (1+(approximatingSolution f hfm (ι n)).kineticProfile p)) 1
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))) := by
  have h := uniformIntegrable_comp
    (approximatingSolution_gain_unit_uniformIntegrable_local f hfm hf hi hT hR)
    (fun n => ι n-Nat.ceil T)
  have he n : ι n-Nat.ceil T+Nat.ceil T = ι n := Nat.sub_add_cancel (hι n)
  convert h using 1
  funext n p
  exact congrArg (fun k : ℕ =>
    gain ((k:ℝ)+1) (approximatingSolution f hfm k).kineticProfile p /
      (1+(approximatingSolution f hfm k).kineticProfile p)) (he n).symm

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual finite physical gains converge locally in measure -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness

theorem GlobalCollisionLimit.gain_in_measure {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (R : ℝ) :
    TendstoInMeasure
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))
      (fun n => gain ((G.weakLimit.indices n:ℝ)+1)
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)
      atTop (gainDensity G.weakLimit.kineticProfile) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let ν : Measure Velocity := volume.restrict (Metric.closedBall 0 R)
  let : IsFiniteMeasure ν :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne
  have hFm (n : ℕ) : Measurable (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
  have hFn (n : ℕ) (p : (ℝ × Position) × Velocity) :
      0 ≤ (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile p :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _
  exact physical_gain_tendstoInMeasure (μ := μ) (ν := ν) hFm
    G.weakLimit.kineticProfile_measurable hFn (fun _ => G.weakLimit.nonnegative _)
    (G.mass_strong T hT) (G.finite_gain_strong hf hi hT R)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Global local-mass balance of the constructed weak density -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalWeakLimit.global_local_mass {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (φ : MassTest) :
    IntegrableOn (fun z : ℝ × Phase => G.density z*φ.transportDerivative z.1 z.2) nonnegativeTimes ∧
    (∫ z in nonnegativeTimes, G.density z*φ.transportDerivative z.1 z.2)+
      (∫ p : Phase, f p*φ.toFun 0 p.1) = 0 := by
  obtain ⟨T,hT,hend,hzero⟩ := φ.exists_time_cutoff
  let u : ℝ × Phase → ℝ := fun z => G.density z*φ.transportDerivative z.1 z.2
  have hui : IntegrableOn u (boundedTimes T) := by
    change Integrable u (volume.restrict (boundedTimes T))
    rw [← phaseInterval_measure]
    exact mass_transport_integrable G.measurable (fun t p => G.nonnegative (t,p))
      (G.entropyMoment_on_window hf hi hT.le) φ
  have hsub : boundedTimes T ⊆ nonnegativeTimes := fun _ hz => ⟨hz.1.1,hz.2⟩
  have hm : MeasurableSet nonnegativeTimes := measurableSet_Ici.prod MeasurableSet.univ
  have hz : ∀ z ∈ nonnegativeTimes \ boundedTimes T, u z = 0 := by
    intro z hz
    have ht : T < z.1 := lt_of_not_ge (fun ht => hz.2 ⟨⟨hz.1.1,ht⟩,hz.1.2⟩)
    change G.density z*φ.transportDerivative z.1 z.2 = 0
    rw [hzero z.1 ht z.2,mul_zero]
  refine ⟨hui.of_forall_sdiff_eq_zero hm hz,?_⟩
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hm hsub hz,← phaseInterval_measure]
  exact G.local_mass_equation hf hi hT.le φ hend

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The normalized gain discrepancy of two actual approximation subsequences vanishes -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem GlobalCollisionLimit.gain_discrepancy_L1 {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (i j : ℕ → ℕ) (hit : Tendsto i atTop atTop) (hjt : Tendsto j atTop atTop) :
    let I := fun n => G.weakLimit.indices (i n+Nat.ceil T)
    let J := fun n => G.weakLimit.indices (j n+Nat.ceil T)
    let U := fun n => (approximatingSolution f hfm (I n)).kineticProfile
    let V := fun n => (approximatingSolution f hfm (J n)).kineticProfile
    Tendsto (fun n => eLpNorm (fun p =>
      (gain ((I n:ℝ)+1) (U n) p-gain ((J n:ℝ)+1) (V n) p)/(1+U n p+V n p))
      1 (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) atTop (𝓝 0) := by
  let ν : Measure Velocity := volume.restrict (Metric.closedBall 0 R)
  let : IsFiniteMeasure ν :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne
  let I := fun n => G.weakLimit.indices (i n+Nat.ceil T)
  let J := fun n => G.weakLimit.indices (j n+Nat.ceil T)
  let U := fun n => (approximatingSolution f hfm (I n)).kineticProfile
  let V := fun n => (approximatingSolution f hfm (J n)).kineticProfile
  have hIm n : Measurable (U n) := (approximatingSolution f hfm (I n)).kineticProfile_measurable
  have hJm n : Measurable (V n) := (approximatingSolution f hfm (J n)).kineticProfile_measurable
  have hIn n p : 0 ≤ U n p := (approximatingSolution f hfm (I n)).nonnegative _
  have hJn n p : 0 ≤ V n p := (approximatingSolution f hfm (J n)).nonnegative _
  have hIc n : Nat.ceil T ≤ I n :=
    (Nat.le_add_left (Nat.ceil T) (i n)).trans (G.weakLimit.increasing.id_le _)
  have hJc n : Nat.ceil T ≤ J n :=
    (Nat.le_add_left (Nat.ceil T) (j n)).trans (G.weakLimit.increasing.id_le _)
  have hi' : Tendsto (fun n => i n+Nat.ceil T) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right (i n) (Nat.ceil T)) hit
  have hj' : Tendsto (fun n => j n+Nat.ceil T) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right (j n) (Nat.ceil T)) hjt
  have ha := (G.gain_in_measure hf hi hT R).comp hi'
  have hb := (G.gain_in_measure hf hi hT R).comp hj'
  apply normalized_source_difference_L1 hIm hJm
    (fun n => gain_measurable _ (hIm n)) (fun n => gain_measurable _ (hJm n)) hIn hJn
    (fun n p => (gain_bounds (by positivity) (hIm n) (hIn n) p).1)
    (fun n p => (gain_bounds (by positivity) (hJm n) (hJn n) p).1) ha hb
  · exact approximatingSolution_subsequence_gain_unit_uniformIntegrable f hfm hf hi hT hR I hIc
  · exact approximatingSolution_subsequence_gain_unit_uniformIntegrable f hfm hf hi hT hR J hJc

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual periodic approximations have vanishing normalized loss defect -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness

theorem GlobalCollisionLimit.loss_residual_L1 {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm (fun p : (ℝ × Position) × Velocity =>
      (lossDensity (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile p-
        loss ((G.weakLimit.indices n:ℝ)+1)
          (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile p)/
        (1+(approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile p)) 1
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let F n := (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile
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
  let N (n : ℕ) : ℝ := (G.weakLimit.indices n:ℝ)+1
  have hN n : 0 < N n := by dsimp [N]; positivity
  have hNt : Tendsto N atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp G.weakLimit.increasing.tendsto_atTop).atTop_add tendsto_const_nhds
  obtain ⟨B,hB⟩ := (approximatingSolution_compactness_hypotheses f hfm hf hi
    (volume.restrict (Icc 0 T))).1.2
  exact lossResidual_L1 hR hFm G.weakLimit.kineticProfile_measurable hFn
    (fun _ => G.weakLimit.nonnegative _) hEi hEb hN hNt B
    (fun n => hB (G.weakLimit.indices n)) (G.mass_strong T hT)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Unit-normalized gain compactness in characteristic coordinates -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem characteristic_gain_unit_uniformIntegrable
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyMoment f)) {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (ι : ℕ → ℕ) (hι : ∀ n, Nat.ceil T ≤ ι n) :
    UniformIntegrable (fun n z =>
      (approximatingSolution f hfm (ι n)).characteristicGain z/
        (1+(approximatingSolution f hfm (ι n)).density (z.1,TorusFlight.flight z.1 z.2))) 1
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) := by
  have h := approximatingSolution_subsequence_gain_unit_uniformIntegrable f hfm hf hi hT hR ι hι
  have hm n : Measurable (fun p =>
      gain ((ι n:ℝ)+1) (approximatingSolution f hfm (ι n)).kineticProfile p/
        (1+(approximatingSolution f hfm (ι n)).kineticProfile p)) :=
    (gain_measurable _ (approximatingSolution f hfm (ι n)).kineticProfile_measurable).div
      (measurable_const.add (approximatingSolution f hfm (ι n)).kineticProfile_measurable)
  have hh := TorusFlight.uniformIntegrable_along_regroup_local
    (μ := volume.restrict (Icc 0 T))
    (ν := (volume : Measure Velocity).restrict (Metric.closedBall 0 R)) hm h
  have he : (fun n => TorusFlight.along (TorusFlight.regroup (fun p =>
      gain ((ι n:ℝ)+1) (approximatingSolution f hfm (ι n)).kineticProfile p/
        (1+(approximatingSolution f hfm (ι n)).kineticProfile p)))) =
      (fun n z => (approximatingSolution f hfm (ι n)).characteristicGain z/
        (1+(approximatingSolution f hfm (ι n)).density (z.1,TorusFlight.flight z.1 z.2))) := by
    funext n z
    rfl
  rw [he] at hh
  exact hh

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
