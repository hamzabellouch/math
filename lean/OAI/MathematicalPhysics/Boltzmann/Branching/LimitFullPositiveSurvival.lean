import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveContributionsIntegrable
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveVolterra
import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicPhysicalGain
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicDensityStrong
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongCompactPairTests
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

section

/-! # The same global weak limit retains every clipped physical positive source -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.positive_survival_lower {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R L : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) (hL : 0 ≤ L) (K : ℝ≥0) :
    ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 L))),
      survivingInitial T f G.weakLimit.kineticProfile z+
        physicalPositiveSource T K R G.weakLimit.kineticProfile z ≤
          G.weakLimit.density (z.1,TorusFlight.flight z.1 z.2) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let ν : Measure Phase := (volume : Measure Position).prod
    ((volume : Measure Velocity).restrict (Metric.closedBall 0 L))
  let F n := (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile
  let a n := survivingInitial T (initialApproximation ((G.weakLimit.indices n:ℝ)+1) f) (F n)
  let b := survivingInitial T f G.weakLimit.kineticProfile
  have hFm n : Measurable (F n) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
  have hFn n q : 0 ≤ F n q :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative (q.1.1,(q.1.2,q.2))
  have hν : ν ≤ (volume : Measure Phase) := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod_mono le_rfl Measure.restrict_le_self
  have hfi : Integrable f := integrable_of_entropyGauge hfm hf hi
  have ha0i n : Integrable (initialApproximation ((G.weakLimit.indices n:ℝ)+1) f) ν := by
    apply (hfi.mono_measure hν).mono'
      (initialApproximation_measurable ((G.weakLimit.indices n:ℝ)+1) hfm).aestronglyMeasurable
    filter_upwards [] with p
    rw [Real.norm_of_nonneg (initialApproximation_bounds
      (N := (G.weakLimit.indices n:ℝ)+1) (by positivity) f p).1]
    exact initialApproximation_le hf p
  have hai n : Integrable (a n) (μ.prod ν) :=
    survivingInitial_integrable T (ha0i n) (hFm n) (hFn n)
  have hbi : Integrable b (μ.prod ν) := survivingInitial_integrable T (hfi.mono_measure hν)
    G.weakLimit.kineticProfile_measurable (fun q => G.weakLimit.nonnegative (q.1.1,(q.1.2,q.2)))
  have hbm : Measurable b :=
    (Published.timeSurvival_measurable
      (physicalCharacteristicFrequency_measurable G.weakLimit.kineticProfile_measurable)).mul
        (hfm.comp measurable_snd)
  have haw := Published.weakL1_of_eLpNorm_sub hai hbm hbi
    (G.surviving_initial_strong hf hi hT hL)
  have hc := G.positive_source_limit hf hi hT hR hL K
  have hci n := G.finitePositiveSource_integrable hf hi hT hR K L n
  have hw := (G.weakLimit.kinetic_weak_on_window hT).restrict
    (s := (univ : Set (ℝ × Position)) ×ˢ Metric.closedBall (0:Velocity) L)
    (MeasurableSet.univ.prod Metric.isClosed_closedBall.measurableSet)
  rw [← Measure.prod_restrict,Measure.restrict_univ] at hw
  have hDw := TorusFlight.weak_along_regroup_local hFm hw
  have hDi n : Integrable (TorusFlight.along (TorusFlight.regroup (F n))) (μ.prod ν) := by
    have hki := integrable_of_entropyGauge (hFm n) (hFn n)
      ((approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integrable
        (μ := μ) (by positivity) (approximatingSolution_entropy f hfm hf hi _))
    exact (TorusFlight.alongRegroup_measurePreserving μ _).integrable_comp_of_integrable
      (hki.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self))
  have hd := (hDw.sub haw hDi hai).sub hc (fun n => (hDi n).sub (hai n)) hci
  have hind : Tendsto (fun n => (G.weakLimit.indices n:ℝ)+1) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp G.weakLimit.increasing.tendsto_atTop).atTop_add tendsto_const_nhds
  have ht : ∀ᵐ z ∂μ.prod ν, z.1 ∈ Icc 0 T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  have he : ∀ᶠ n in atTop, (fun _ : ℝ × Phase => (0:ℝ)) ≤ᵐ[μ.prod ν]
      (fun z => (TorusFlight.along (TorusFlight.regroup (F n)) z-a n z)-
        finitePositiveSource T ((G.weakLimit.indices n:ℝ)+1) K R (F n) z) := by
    filter_upwards [hind.eventually (eventually_ge_atTop T)] with n hn
    filter_upwards [ht] with z hz
    have h := (approximatingSolution f hfm (G.weakLimit.indices n)).clipped_positive_survival
      (R := R) (by positivity) hn hz K.coe_nonneg z.2
    change 0 ≤ (TorusFlight.along (TorusFlight.regroup (F n)) z-a n z)-
      finitePositiveSource T ((G.weakLimit.indices n:ℝ)+1) K R (F n) z
    change a n z+finitePositiveSource T ((G.weakLimit.indices n:ℝ)+1) K R (F n) z ≤
      TorusFlight.along (TorusFlight.regroup (F n)) z at h
    linarith
  have h := hd.ge_eventually (fun n => ((hDi n).sub (hai n)).sub (hci n))
    measurable_const (fun _ => le_rfl) he
  filter_upwards [h] with z hz
  change 0 ≤ (G.weakLimit.density (z.1,TorusFlight.flight z.1 z.2)-b z)-
    physicalPositiveSource T K R G.weakLimit.kineticProfile z at hz
  change b z+physicalPositiveSource T K R G.weakLimit.kineticProfile z ≤ _
  linarith

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual weak limit retains the full physical positive characteristic source -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

def physicalFullPositiveSource (T : ℝ) (f : (ℝ × Position) × Velocity → ℝ) : ℝ × Phase → ℝ :=
  Published.survivalVolterra (volume.restrict (Icc 0 T))
    (Published.twoTimeSurvival (volume.restrict (Icc 0 T)) (physicalCharacteristicFrequency f))
    (physicalCharacteristicGain f)

theorem GlobalCollisionLimit.full_positive_survival_lower {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T L : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) :
    ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 L))),
      Integrable (fun s => if s ≤ z.1 then
        Published.twoTimeSurvival (volume.restrict (Icc 0 T))
          (physicalCharacteristicFrequency G.weakLimit.kineticProfile) (z,s)*
            physicalCharacteristicGain G.weakLimit.kineticProfile (s,z.2) else 0)
          (volume.restrict (Icc 0 T)) ∧
      survivingInitial T f G.weakLimit.kineticProfile z+
        physicalFullPositiveSource T G.weakLimit.kineticProfile z ≤
          G.weakLimit.density (z.1,TorusFlight.flight z.1 z.2) := by
  have hn : ∀ q, 0 ≤ G.weakLimit.kineticProfile q := fun _ => G.weakLimit.nonnegative _
  apply Published.positive_volterra_limit
    (f := fun n : ℕ => characteristicClippedPhysicalGain (n:ℝ) (n:ℝ) G.weakLimit.kineticProfile)
    (fun n => (G.characteristic_clipped_gain_limit hf hi hT (Nat.cast_nonneg n) (n:ℝ≥0) L).1.2.1)
    (fun n z => clippedPhysicalGain_nonneg (Nat.cast_nonneg n) hn _)
    (physicalCharacteristicGain_measurable G.weakLimit.kineticProfile_measurable)
    (physicalCharacteristicGain_nonneg hn)
    (Published.twoTimeSurvival_measurable
      (physicalCharacteristicFrequency_measurable G.weakLimit.kineticProfile_measurable))
    (fun z => ⟨(Published.twoTimeSurvival_bounds _ _ z).1.le,
      (Published.twoTimeSurvival_bounds _ _ z).2⟩)
    (G.characteristic_clipped_gain_tendsto hf hi hT L)
    (fun n => G.positive_survival_lower hf hi hT (Nat.cast_nonneg n) hL (n:ℝ≥0))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
