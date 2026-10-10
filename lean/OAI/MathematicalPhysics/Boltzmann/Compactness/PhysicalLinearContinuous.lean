import OAI.MathematicalPhysics.Boltzmann.Approximation.SurvivalProfile
import OAI.MathematicalPhysics.Boltzmann.Approximation.SurvivalVolterraIntegrable
import OAI.MathematicalPhysics.Boltzmann.Branching.IntegrablePathTrace
import OAI.MathematicalPhysics.Boltzmann.Branching.LimitFullPositiveSurvival
import OAI.MathematicalPhysics.Boltzmann.Branching.LinearCharacteristicBalance
import OAI.MathematicalPhysics.Boltzmann.Branching.LinearSurvivalIdentity
import OAI.MathematicalPhysics.Boltzmann.Branching.MaxwellianFrequency
import OAI.MathematicalPhysics.Boltzmann.Branching.NonnegativeGainCongruence
import OAI.MathematicalPhysics.Boltzmann.Branching.TimeSourceCumulative
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityWeight
import OAI.MathematicalPhysics.Boltzmann.Compactness.MeasurableResolvent
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicStrongAverages
import OAI.MathematicalPhysics.Boltzmann.Compactness.RenormalizedIntegrability
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTransport
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusVelocityWindowAE

namespace OAI

section

/-! # Maxwellian-weighted frequency along all physical flights -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem GlobalCollisionLimit.weighted_frequency_integrable
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun z : ℝ × Phase => maxwellian z.2.2*
      physicalCharacteristicFrequency G.weakLimit.kineticProfile z)
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := by
  let μ := volume.restrict (Icc 0 T)
  have hkin := maxwellian_kineticFrequency_integrable G.weakLimit.kineticProfile_measurable
    (fun p => G.weakLimit.nonnegative _) (linearMoment_integrable
      G.weakLimit.kineticProfile_measurable (fun p => G.weakLimit.nonnegative _)
      (G.weakLimit.kinetic_entropy_on_window hf hi hT))
  have h := (TorusFlight.alongRegroup_measurePreserving μ (volume : Measure Velocity)).integrable_comp_of_integrable hkin
  change Integrable (fun z : ℝ × Phase => maxwellian z.2.2*
    physicalCharacteristicFrequency G.weakLimit.kineticProfile z)
    (μ.prod ((volume : Measure Position).prod (volume : Measure Velocity))) at h
  simpa only [Measure.volume_eq_prod] using h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual full physical gain is integrable on almost every finite flight -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.gain_path_integrable {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T L : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) :
    ∀ᵐ p ∂(volume : Measure Position).prod
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 L)),
      Integrable (fun s => physicalCharacteristicGain G.weakLimit.kineticProfile (s,p))
        (volume.restrict (Icc 0 T)) := by
  apply Published.integrable_window_of_ae_prefix hT
  filter_upwards [G.full_positive_survival_lower hf hi (by linarith : 0 ≤ T+1) hL] with z hz
  exact Published.survival_source_unweight
    (physicalCharacteristicFrequency_nonneg (fun _ => G.weakLimit.nonnegative _))
    (physicalCharacteristicGain_measurable G.weakLimit.kineticProfile_measurable)
    (physicalCharacteristicGain_nonneg (fun _ => G.weakLimit.nonnegative _)) z hz.1

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # A common full-measure set of flights with locally integrable gain and frequency -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.gain_path_integrable_full {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ p ∂(volume : Measure Phase),
      Integrable (fun s => physicalCharacteristicGain G.weakLimit.kineticProfile (s,p))
        (volume.restrict (Icc 0 T)) := by
  rw [Measure.volume_eq_prod]
  exact ae_prod_of_velocity_windows (fun n => G.gain_path_integrable hf hi hT (Nat.cast_nonneg n))

theorem GlobalCollisionLimit.frequency_path_integrable_full {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ p ∂(volume : Measure Phase),
      Integrable (fun s => physicalCharacteristicFrequency G.weakLimit.kineticProfile (s,p))
        (volume.restrict (Icc 0 T)) := by
  rw [Measure.volume_eq_prod]
  exact ae_prod_of_velocity_windows (fun n =>
    (G.characteristic_frequency_integrable hf hi hT (Nat.cast_nonneg n)).2.prod_left_ae)

theorem GlobalCollisionLimit.flight_integrable_locally {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ p ∂(volume : Measure Phase), ∀ T : ℝ, 0 ≤ T →
      Integrable (fun s => physicalCharacteristicGain G.weakLimit.kineticProfile (s,p))
        (volume.restrict (Icc 0 T)) ∧
      Integrable (fun s => physicalCharacteristicFrequency G.weakLimit.kineticProfile (s,p))
        (volume.restrict (Icc 0 T)) := by
  have hg : ∀ᵐ p ∂(volume : Measure Phase), ∀ n : ℕ,
      Integrable (fun s => physicalCharacteristicGain G.weakLimit.kineticProfile (s,p))
        (volume.restrict (Icc 0 (n:ℝ))) ∧
      Integrable (fun s => physicalCharacteristicFrequency G.weakLimit.kineticProfile (s,p))
        (volume.restrict (Icc 0 (n:ℝ))) := by
    rw [ae_all_iff]
    intro n
    exact (G.gain_path_integrable_full hf hi (Nat.cast_nonneg n)).and
      (G.frequency_path_integrable_full hf hi (Nat.cast_nonneg n))
  filter_upwards [hg] with p hp
  intro T _hT
  obtain ⟨n,hn⟩ := exists_nat_ge T
  have hm : (volume : Measure ℝ).restrict (Icc 0 T) ≤ volume.restrict (Icc 0 (n:ℝ)) :=
    Measure.restrict_mono (Icc_subset_Icc le_rfl hn) le_rfl
  exact ⟨(hp n).1.mono_measure hm,(hp n).2.mono_measure hm⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual linear characteristic profile is a lower solution for the weak limit -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def physicalLinearProfile (f₀ : Density) (F : (ℝ × Position) × Velocity → ℝ)
    (z : ℝ × Phase) : ℝ :=
  TransportPrimitive.linearSolution (f₀ z.2)
    (fun s => physicalCharacteristicFrequency F (s,z.2))
    (fun s => physicalCharacteristicGain F (s,z.2)) z.1

theorem physicalLinearProfile_initial (f₀ : Density) (F : (ℝ × Position) × Velocity → ℝ)
    (p : Phase) : physicalLinearProfile f₀ F (0,p) = f₀ p :=
  TransportPrimitive.linearSolution_initial _ _ _

theorem GlobalCollisionLimit.linear_profile_absolutelyContinuous
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ p ∂(volume : Measure Phase), ∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval
        (fun t => physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) 0 T := by
  filter_upwards [G.flight_integrable_locally hf hi] with p hp
  intro T hT
  have hk : IntervalIntegrable (fun s => physicalCharacteristicFrequency G.weakLimit.kineticProfile (s,p))
      volume 0 T := (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr (hp T hT).2
  have hg : IntervalIntegrable (fun s => physicalCharacteristicGain G.weakLimit.kineticProfile (s,p))
      volume 0 T := (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr (hp T hT).1
  change AbsolutelyContinuousOnInterval
    (TransportPrimitive.linearSolution (f p)
      (fun s => physicalCharacteristicFrequency G.weakLimit.kineticProfile (s,p))
      (fun s => physicalCharacteristicGain G.weakLimit.kineticProfile (s,p))) 0 T
  exact TransportPrimitive.linearSolution_absolutelyContinuous (f p) hk hg

theorem GlobalCollisionLimit.linear_profile_eq_source {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T L : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) :
    ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 L))),
      physicalLinearProfile f G.weakLimit.kineticProfile z =
        survivingInitial T f G.weakLimit.kineticProfile z+
          physicalFullPositiveSource T G.weakLimit.kineticProfile z := by
  have hfreq := (G.characteristic_frequency_integrable hf hi hT hL).2.prod_left_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hfreq,
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with z hz ht
  exact Published.linearSolution_eq_survival ht (f z.2)
    (physicalCharacteristicFrequency_nonneg (fun _ => G.weakLimit.nonnegative _)) _ z.2
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hz)

theorem GlobalCollisionLimit.linear_profile_le {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T L : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) :
    ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 L))),
      physicalLinearProfile f G.weakLimit.kineticProfile z ≤
        G.weakLimit.density (z.1,TorusFlight.flight z.1 z.2) := by
  filter_upwards [G.linear_profile_eq_source hf hi hT hL,
    G.full_positive_survival_lower hf hi hT hL] with z he hb
  exact he.trans_le hb.2

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The linear characteristic lower profile has the physical forcing and loss -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem physicalLinearProfile_nonneg {f : Density} (hf : ∀ p, 0 ≤ f p)
    {F : (ℝ × Position) × Velocity → ℝ} (hF : ∀ p, 0 ≤ F p)
    {t : ℝ} (ht : 0 ≤ t) (p : Phase) : 0 ≤ physicalLinearProfile f F (t,p) := by
  unfold physicalLinearProfile TransportPrimitive.linearSolution
  apply mul_nonneg (Real.exp_pos _).le
  apply add_nonneg (hf p)
  exact intervalIntegral.integral_nonneg ht (fun s _ =>
    mul_nonneg (Real.exp_pos _).le (physicalCharacteristicGain_nonneg hF _))

theorem GlobalCollisionLimit.linear_profile_hasDerivAt_ae
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ p ∂(volume : Measure Phase), ∀ T : ℝ, 0 ≤ T →
      ∀ᵐ t ∂volume, t ∈ Icc 0 T →
        HasDerivAt (fun s => physicalLinearProfile f G.weakLimit.kineticProfile (s,p))
          (physicalCharacteristicGain G.weakLimit.kineticProfile (t,p)-
            physicalCharacteristicFrequency G.weakLimit.kineticProfile (t,p)*
              physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) t := by
  filter_upwards [G.flight_integrable_locally hf hi] with p hp
  intro T hT
  have hk : IntervalIntegrable (fun s => physicalCharacteristicFrequency G.weakLimit.kineticProfile (s,p))
      volume 0 T := (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr (hp T hT).2
  have hg : IntervalIntegrable (fun s => physicalCharacteristicGain G.weakLimit.kineticProfile (s,p))
      volume 0 T := (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr (hp T hT).1
  simpa only [physicalLinearProfile] using
    TransportPrimitive.linearSolution_hasDerivAt_ae hT (f p) hk hg

theorem GlobalCollisionLimit.linear_profile_source_integrable
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ p ∂(volume : Measure Phase), ∀ T : ℝ, 0 ≤ T →
      IntervalIntegrable (fun t => physicalCharacteristicGain G.weakLimit.kineticProfile (t,p)-
        physicalCharacteristicFrequency G.weakLimit.kineticProfile (t,p)*
          physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) volume 0 T := by
  filter_upwards [G.flight_integrable_locally hf hi,G.linear_profile_absolutelyContinuous hf hi] with p hp hu
  intro T hT
  have hg := (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr (hp T hT).1
  have hk := (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr (hp T hT).2
  exact hg.sub (hk.mul_continuousOn (hu T hT).continuousOn)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual linear lower profile is measurable and integrable on finite windows -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem physicalFullPositiveSource_measurable (T : ℝ) {F : (ℝ × Position) × Velocity → ℝ}
    (hF : Measurable F) : Measurable (physicalFullPositiveSource T F) :=
  Published.survivalVolterra_measurable
    (Published.twoTimeSurvival_measurable (physicalCharacteristicFrequency_measurable hF))
    (physicalCharacteristicGain_measurable hF)

theorem GlobalCollisionLimit.linear_profile_eq_source_full {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    physicalLinearProfile f G.weakLimit.kineticProfile =ᵐ[(volume.restrict (Icc 0 T)).prod
      (volume : Measure Phase)] fun z => survivingInitial T f G.weakLimit.kineticProfile z+
        physicalFullPositiveSource T G.weakLimit.kineticProfile z :=
  ae_timePhase_of_velocity_windows (fun n => G.linear_profile_eq_source hf hi hT (Nat.cast_nonneg n))

theorem GlobalCollisionLimit.linear_profile_le_full {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase),
      physicalLinearProfile f G.weakLimit.kineticProfile z ≤
        G.weakLimit.density (z.1,TorusFlight.flight z.1 z.2) :=
  ae_timePhase_of_velocity_windows (fun n => G.linear_profile_le hf hi hT (Nat.cast_nonneg n))

theorem GlobalCollisionLimit.linear_profile_integrable {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (physicalLinearProfile f G.weakLimit.kineticProfile)
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hm : Measurable (fun z => survivingInitial T f G.weakLimit.kineticProfile z+
      physicalFullPositiveSource T G.weakLimit.kineticProfile z) :=
    ((Published.timeSurvival_measurable (physicalCharacteristicFrequency_measurable
      G.weakLimit.kineticProfile_measurable)).mul (hfm.comp measurable_snd)).add
        (physicalFullPositiveSource_measurable T G.weakLimit.kineticProfile_measurable)
  have hU : AEStronglyMeasurable (physicalLinearProfile f G.weakLimit.kineticProfile)
      (μ.prod (volume : Measure Phase)) :=
    hm.aestronglyMeasurable.congr (G.linear_profile_eq_source_full hf hi hT).symm
  have hdi := (G.weakLimit.weak_on_window hT).2.1
  have hflight : Integrable (fun z : ℝ × Phase => G.weakLimit.density
      (z.1,TorusFlight.flight z.1 z.2)) (μ.prod (volume : Measure Phase)) := by
    rw [Measure.volume_eq_prod] at hdi ⊢
    exact (TorusFlight.along_measurePreserving_velocity μ (volume : Measure Velocity)).integrable_comp_of_integrable hdi
  apply hflight.mono' hU
  filter_upwards [G.linear_profile_le_full hf hi hT,
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with z hz ht
  have hn : 0 ≤ physicalLinearProfile f G.weakLimit.kineticProfile z :=
    physicalLinearProfile_nonneg (F := G.weakLimit.kineticProfile) hf
      (fun _ => G.weakLimit.nonnegative _) ht.1 z.2
  rw [Real.norm_of_nonneg hn]
  exact hz

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual characteristic profile has a renormalized gain bound -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_profile_log_gain_bound
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ p ∂(volume : Measure Phase), ∀ T : ℝ, 0 ≤ T →
      (∫ t in 0..T, physicalCharacteristicGain G.weakLimit.kineticProfile (t,p)/
        (1+physicalLinearProfile f G.weakLimit.kineticProfile (t,p)/maxwellian p.2)) ≤
      physicalLinearProfile f G.weakLimit.kineticProfile (T,p)+
        maxwellian p.2*(∫ t in 0..T, physicalCharacteristicFrequency G.weakLimit.kineticProfile (t,p)) := by
  filter_upwards [G.flight_integrable_locally hf hi,G.linear_profile_absolutelyContinuous hf hi,
    G.linear_profile_hasDerivAt_ae hf hi] with p hp hU hd
  intro T hT
  apply TransportPrimitive.logarithmic_gain_bound hT (maxwellian_pos p.2) (hU T hT)
    (fun t ht => physicalLinearProfile_nonneg (F := G.weakLimit.kineticProfile) hf
      (fun _ => G.weakLimit.nonnegative _) ht.1 p)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr (hp T hT).2)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr (hp T hT).1)
    (fun t _ => physicalCharacteristicFrequency_nonneg (fun _ => G.weakLimit.nonnegative _) (t,p))
    (hd T hT)


theorem GlobalCollisionLimit.linear_profile_normalized_gain_paths
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ p ∂(volume : Measure Phase), ∀ T : ℝ, 0 ≤ T →
      IntervalIntegrable (fun t => physicalCharacteristicGain G.weakLimit.kineticProfile (t,p)/
        (1+physicalLinearProfile f G.weakLimit.kineticProfile (t,p)/maxwellian p.2)) volume 0 T := by
  filter_upwards [G.flight_integrable_locally hf hi,G.linear_profile_absolutelyContinuous hf hi] with p hp hU
  intro T hT
  have hu : ContinuousOn (fun t => physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) (uIcc 0 T) :=
    (hU T hT).continuousOn
  have hc : ContinuousOn (fun t => (1+physicalLinearProfile f G.weakLimit.kineticProfile (t,p)/maxwellian p.2)⁻¹)
      (uIcc 0 T) := (continuousOn_const.add (hu.div_const _)).inv₀ (by
    intro t ht
    have ht0 : 0 ≤ t := (show t ∈ Icc 0 T by simpa only [uIcc_of_le hT] using ht).1
    have hn := physicalLinearProfile_nonneg (F := G.weakLimit.kineticProfile) hf
      (fun _ => G.weakLimit.nonnegative _) ht0 p
    have hm := maxwellian_pos p.2
    exact (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hn hm.le)).ne')
  have hg := (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr (hp T hT).1
  simpa only [div_eq_mul_inv] using hg.mul_continuousOn hc

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Global renormalized gain integrability for the actual linear profile -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_normalized_gain_integrable_of_slice
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {S : ℝ} (hS : 0 ≤ S)
    (hUi : Integrable (fun p : Phase => physicalLinearProfile f G.weakLimit.kineticProfile (S,p))) :
    Integrable (fun z : ℝ × Phase => physicalCharacteristicGain G.weakLimit.kineticProfile z /
      (1+physicalLinearProfile f G.weakLimit.kineticProfile z/maxwellian z.2.2))
      ((volume.restrict (Icc 0 S)).prod (volume : Measure Phase)) := by
  let U := physicalLinearProfile f G.weakLimit.kineticProfile
  let a := physicalCharacteristicGain G.weakLimit.kineticProfile
  let k := physicalCharacteristicFrequency G.weakLimit.kineticProfile
  have hUm := (G.linear_profile_integrable hf hi hS).aestronglyMeasurable
  have hMm : Measurable (fun z : ℝ × Phase => maxwellian z.2.2) := by unfold maxwellian; fun_prop
  have hAm : AEStronglyMeasurable a ((volume.restrict (Icc 0 S)).prod (volume : Measure Phase)) := (physicalCharacteristicGain_measurable G.weakLimit.kineticProfile_measurable).aestronglyMeasurable
  have hB : Integrable (fun p : Phase => U (S,p)+maxwellian p.2*(∫ t in Icc 0 S, k (t,p))) := by
    have hW := (G.weighted_frequency_integrable hf hi hS).integral_prod_right
    have he : (fun p : Phase => ∫ t in Icc 0 S, maxwellian p.2*k (t,p)) =
        (fun p => maxwellian p.2*(∫ t in Icc 0 S, k (t,p))) := by
      funext p
      exact integral_const_mul _ _
    rw [he] at hW
    exact hUi.add hW
  have hnorm : AEStronglyMeasurable (fun z => a z/(1+U z/maxwellian z.2.2))
      ((volume.restrict (Icc 0 S)).prod (volume : Measure Phase)) :=
    (hAm.aemeasurable.div (aemeasurable_const.add (hUm.aemeasurable.div hMm.aemeasurable))).aestronglyMeasurable
  apply integrable_nonnegative_of_fiber_bound hnorm
    (B := fun p : Phase => U (S,p)+maxwellian p.2*(∫ t in Icc 0 S, k (t,p)))
  · intro p t ht
    have hn := physicalLinearProfile_nonneg (F := G.weakLimit.kineticProfile) hf
      (fun _ => G.weakLimit.nonnegative _) ht.1 p
    have hm := maxwellian_pos p.2
    exact div_nonneg (physicalCharacteristicGain_nonneg (fun _ => G.weakLimit.nonnegative _) _)
      (by positivity)
  · filter_upwards [G.linear_profile_normalized_gain_paths hf hi] with p hp
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hS).mp (hp S hS)
  · exact hB
  · filter_upwards [G.linear_profile_log_gain_bound hf hi] with p hp
    have hb := hp S hS
    rw [intervalIntegral.integral_of_le hS,← integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hS,← integral_Icc_eq_integral_Ioc] at hb
    exact hb

theorem GlobalCollisionLimit.linear_normalized_gain_integrable
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun z : ℝ × Phase => physicalCharacteristicGain G.weakLimit.kineticProfile z /
      (1+physicalLinearProfile f G.weakLimit.kineticProfile z/maxwellian z.2.2))
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := by
  have hU := (G.linear_profile_integrable hf hi (show 0 ≤ T+1 by linarith)).prod_right_ae
  have hs : Ioo T (T+1) ⊆ Icc 0 (T+1) := fun s hs => ⟨hT.trans hs.1.le,hs.2.le⟩
  have hpos : (volume : Measure ℝ) (Ioo T (T+1)) ≠ 0 := by rw [Real.volume_Ioo]; norm_num
  have hUs := hU.filter_mono (ae_mono (Measure.restrict_mono hs le_rfl))
  obtain ⟨S,hS,hSi⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos hUs
  have hg := G.linear_normalized_gain_integrable_of_slice hf hi (hT.trans hS.1.le) hSi
  exact hg.mono_measure (Measure.prod_mono
    (Measure.restrict_mono (Icc_subset_Icc le_rfl hS.1.le) le_rfl) le_rfl)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Separate normalized loss integrability for the actual characteristic profile -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_normalized_loss_integrable
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun z : ℝ × Phase =>
      physicalCharacteristicFrequency G.weakLimit.kineticProfile z*
        physicalLinearProfile f G.weakLimit.kineticProfile z /
          (1+physicalLinearProfile f G.weakLimit.kineticProfile z/maxwellian z.2.2))
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := by
  let U := physicalLinearProfile f G.weakLimit.kineticProfile
  let k := physicalCharacteristicFrequency G.weakLimit.kineticProfile
  have hUm := (G.linear_profile_integrable hf hi hT).aestronglyMeasurable
  have hMm : Measurable (fun z : ℝ × Phase => maxwellian z.2.2) := by unfold maxwellian; fun_prop
  have hkm : AEStronglyMeasurable k ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := (physicalCharacteristicFrequency_measurable G.weakLimit.kineticProfile_measurable).aestronglyMeasurable
  have hnorm : AEStronglyMeasurable (fun z => k z*U z/(1+U z/maxwellian z.2.2))
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) :=
    ((hkm.aemeasurable.mul hUm.aemeasurable).div
      (aemeasurable_const.add (hUm.aemeasurable.div hMm.aemeasurable))).aestronglyMeasurable
  apply (G.weighted_frequency_integrable hf hi hT).mono' hnorm
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with z hz
  have hu : 0 ≤ U z := physicalLinearProfile_nonneg (F := G.weakLimit.kineticProfile) hf
    (fun _ => G.weakLimit.nonnegative _) hz.1 z.2
  have hk : 0 ≤ k z := physicalCharacteristicFrequency_nonneg (fun _ => G.weakLimit.nonnegative _) z
  have hm := maxwellian_pos z.2.2
  have hd : 0 < 1+U z/maxwellian z.2.2 := by positivity
  change ‖k z*U z/(1+U z/maxwellian z.2.2)‖ ≤ maxwellian z.2.2*k z
  rw [Real.norm_of_nonneg (by positivity)]
  have hb : U z/(1+U z/maxwellian z.2.2) ≤ maxwellian z.2.2 := by
    apply (div_le_iff₀ hd).mpr
    field_simp
    nlinarith
  calc
    _ = k z*(U z/(1+U z/maxwellian z.2.2)) := by ring
    _ ≤ k z*maxwellian z.2.2 := mul_le_mul_of_nonneg_left hb hk
    _ = _ := mul_comm _ _

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual linear profile satisfies every tested renormalized path identity -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_renormalized_tested_paths
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (β : Renormalization) (φ : KineticTest) :
    ∀ᵐ p ∂(volume : Measure Phase),
      (∫ t in 0..T,
        derivWithin β.toFun (Ici 0)
          (physicalLinearProfile f G.weakLimit.kineticProfile (t,p)/maxwellian p.2)*
          (physicalCharacteristicGain G.weakLimit.kineticProfile (t,p)-
            physicalCharacteristicFrequency G.weakLimit.kineticProfile (t,p)*
              physicalLinearProfile f G.weakLimit.kineticProfile (t,p))*
          φ.toFun t (TorusFlight.flight t p).1 p.2+
        maxwellian p.2*β.toFun (physicalLinearProfile f G.weakLimit.kineticProfile (t,p)/maxwellian p.2)*
          φ.transportDerivative t (TorusFlight.flight t p)) =
      maxwellian p.2*β.toFun (physicalLinearProfile f G.weakLimit.kineticProfile (T,p)/maxwellian p.2)*
        φ.toFun T (TorusFlight.flight T p).1 p.2-
      maxwellian p.2*β.toFun (f p/maxwellian p.2)*φ.toFun 0 p.1 p.2 := by
  filter_upwards [G.linear_profile_absolutelyContinuous hf hi,G.linear_profile_hasDerivAt_ae hf hi]
    with p hU hd
  have hφ : AbsolutelyContinuousOnInterval
      (fun t => φ.toFun t (TorusFlight.flight t p).1 p.2) 0 T :=
    ((φ.contDiff_along p).of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hφ' : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt
      (fun t => φ.toFun t (TorusFlight.flight t p).1 p.2)
      (φ.transportDerivative t (TorusFlight.flight t p)) t :=
    ae_of_all _ (fun t _ => φ.hasDerivAt_along p t)
  simpa only [physicalLinearProfile_initial,TorusFlight.flight_zero] using
    β.weighted_tested_chain_rule hT (maxwellian_pos p.2) (hU T hT)
      (fun t ht => physicalLinearProfile_nonneg (F := G.weakLimit.kineticProfile) hf
        (fun _ => G.weakLimit.nonnegative _) ht.1 p) (hd T hT) hφ hφ'

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Every manuscript renormalization has an integrable linear characteristic source -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_renormalized_source_integrable
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (β : Renormalization) :
    Integrable (fun z : ℝ × Phase =>
      derivWithin β.toFun (Ici 0)
        (physicalLinearProfile f G.weakLimit.kineticProfile z/maxwellian z.2.2)*
      (physicalCharacteristicGain G.weakLimit.kineticProfile z-
        physicalCharacteristicFrequency G.weakLimit.kineticProfile z*
          physicalLinearProfile f G.weakLimit.kineticProfile z))
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := by
  have hMm : Measurable (fun z : ℝ × Phase => maxwellian z.2.2) := by unfold maxwellian; fun_prop
  have hU := (G.linear_profile_integrable hf hi hT).aestronglyMeasurable
  have hn : ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase),
      0 ≤ physicalLinearProfile f G.weakLimit.kineticProfile z/maxwellian z.2.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with z hz
    exact div_nonneg (physicalLinearProfile_nonneg (F := G.weakLimit.kineticProfile) hf
      (fun _ => G.weakLimit.nonnegative _) hz.1 z.2) (maxwellian_pos _).le
  have ha := β.derivative_mul_integrable_of_normalized (hU.aemeasurable.div hMm.aemeasurable).aestronglyMeasurable hn
    (G.linear_normalized_gain_integrable hf hi hT)
  have hl := β.derivative_mul_integrable_of_normalized (hU.aemeasurable.div hMm.aemeasurable).aestronglyMeasurable hn
    (G.linear_normalized_loss_integrable hf hi hT)
  convert ha.sub hl using 1
  funext z
  exact mul_sub _ _ _

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Integrable tested fields for the actual linear characteristic equation -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def linearRenormalizedField (f : Density) (F : (ℝ × Position) × Velocity → ℝ)
    (β : Renormalization) (φ : KineticTest) (z : ℝ × Phase) : ℝ :=
  maxwellian z.2.2*β.toFun (physicalLinearProfile f F z/maxwellian z.2.2)*
    φ.transportDerivative z.1 (TorusFlight.flight z.1 z.2)+
  derivWithin β.toFun (Ici 0) (physicalLinearProfile f F z/maxwellian z.2.2)*
    (physicalCharacteristicGain F z-physicalCharacteristicFrequency F z*physicalLinearProfile f F z)*
    φ.toFun z.1 (TorusFlight.flight z.1 z.2).1 z.2.2

theorem GlobalCollisionLimit.linear_renormalized_field_integrable
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (β : Renormalization) (φ : KineticTest) :
    Integrable (linearRenormalizedField f G.weakLimit.kineticProfile β φ)
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := by
  let μ := volume.restrict (Icc 0 T)
  have hMm : Measurable (fun z : ℝ × Phase => maxwellian z.2.2) := by unfold maxwellian; fun_prop
  have ht : ∀ᵐ z ∂μ.prod (volume : Measure Phase), z.1 ∈ Icc 0 T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  have hn : ∀ᵐ z ∂μ.prod (volume : Measure Phase), 0 ≤ physicalLinearProfile f G.weakLimit.kineticProfile z := by
    filter_upwards [ht] with z hz
    exact physicalLinearProfile_nonneg (F := G.weakLimit.kineticProfile) hf
      (fun _ => G.weakLimit.nonnegative _) hz.1 z.2
  have hwi := β.weighted_integrable_of_ae hMm (fun z => maxwellian_pos z.2.2) hn
    (G.linear_profile_integrable hf hi hT)
  have hsrc := G.linear_renormalized_source_integrable hf hi hT β
  have hφm : Measurable (fun z : ℝ × Phase => φ.toFun z.1 (TorusFlight.flight z.1 z.2).1 z.2.2) :=
    φ.measurable_toFun.comp (TorusFlight.along_measurePreserving μ).measurable
  have hDm : Measurable (fun z : ℝ × Phase => φ.transportDerivative z.1 (TorusFlight.flight z.1 z.2)) :=
    φ.measurable_transportDerivative.comp (TorusFlight.along_measurePreserving μ).measurable
  obtain ⟨C,_,hC⟩ := φ.bounded_on_time T
  have hφb : ∀ᵐ z ∂μ.prod (volume : Measure Phase),
      ‖φ.toFun z.1 (TorusFlight.flight z.1 z.2).1 z.2.2‖ ≤ C := by
    filter_upwards [ht] with z hz
    exact (hC z.1 hz (TorusFlight.flight z.1 z.2)).1
  have hDb : ∀ᵐ z ∂μ.prod (volume : Measure Phase),
      ‖φ.transportDerivative z.1 (TorusFlight.flight z.1 z.2)‖ ≤ C := by
    filter_upwards [ht] with z hz
    exact (hC z.1 hz (TorusFlight.flight z.1 z.2)).2
  exact (hwi.mul_bdd hDm.aestronglyMeasurable hDb).add
    (hsrc.mul_bdd hφm.aestronglyMeasurable hφb)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Integral paths of every renormalization of the actual linear profile -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def linearRenormalizedDensity (f : Density) (F : (ℝ × Position) × Velocity → ℝ)
    (β : Renormalization) (z : ℝ × Phase) : ℝ :=
  maxwellian z.2.2*β.toFun (physicalLinearProfile f F z/maxwellian z.2.2)

def linearRenormalizedSource (f : Density) (F : (ℝ × Position) × Velocity → ℝ)
    (β : Renormalization) (z : ℝ × Phase) : ℝ :=
  derivWithin β.toFun (Ici 0) (physicalLinearProfile f F z/maxwellian z.2.2)*
    (physicalCharacteristicGain F z-physicalCharacteristicFrequency F z*physicalLinearProfile f F z)

theorem GlobalCollisionLimit.linear_renormalized_integral_paths
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (β : Renormalization) :
    ∀ᵐ p ∂(volume : Measure Phase), ∀ t : ℝ, 0 ≤ t →
      linearRenormalizedDensity f G.weakLimit.kineticProfile β (t,p) =
        maxwellian p.2*β.toFun (f p/maxwellian p.2)+
          ∫ s in 0..t, linearRenormalizedSource f G.weakLimit.kineticProfile β (s,p) := by
  filter_upwards [G.linear_profile_absolutelyContinuous hf hi,G.linear_profile_hasDerivAt_ae hf hi]
    with p hU hd
  intro t ht
  have he := β.weighted_chain_rule ht (maxwellian_pos p.2) (hU t ht)
    (fun s hs => physicalLinearProfile_nonneg (F := G.weakLimit.kineticProfile) hf
      (fun _ => G.weakLimit.nonnegative _) hs.1 p) (hd t ht)
  rw [physicalLinearProfile_initial] at he
  change (∫ s in 0..t, linearRenormalizedSource f G.weakLimit.kineticProfile β (s,p)) =
    linearRenormalizedDensity f G.weakLimit.kineticProfile β (t,p)-
      maxwellian p.2*β.toFun (f p/maxwellian p.2) at he
  linarith

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Tested renormalized balance for the actual linear characteristic profile -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_renormalized_balance_terminal_zero
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (β : Renormalization) (φ : KineticTest)
    (hφ : ∀ x v, φ.toFun T x v = 0) :
    (∫ z, linearRenormalizedField f G.weakLimit.kineticProfile β φ z
      ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase))+
      (∫ p : Phase, maxwellian p.2*β.toFun (f p/maxwellian p.2)*φ.toFun 0 p.1 p.2) = 0 := by
  have hI := G.linear_renormalized_field_integrable hf hi hT β φ
  have hinit := φ.weighted_slice_integrable β (T := T) ⟨le_rfl,hT⟩ hfm hf
    (show Integrable f from (show FiniteEntropyDatum f from ⟨ae_of_all _ hf,hfm.aestronglyMeasurable,hi⟩).integrable)
  have hp : ∀ᵐ p ∂(volume : Measure Phase),
      (∫ t in Icc 0 T, linearRenormalizedField f G.weakLimit.kineticProfile β φ (t,p)) =
        -(maxwellian p.2*β.toFun (f p/maxwellian p.2)*φ.toFun 0 p.1 p.2) := by
    filter_upwards [G.linear_renormalized_tested_paths hf hi hT β φ] with p hp
    rw [hφ,mul_zero,zero_sub,intervalIntegral.integral_of_le hT,← integral_Icc_eq_integral_Ioc] at hp
    rw [← hp]
    apply integral_congr_ae
    exact ae_of_all _ (fun t => by unfold linearRenormalizedField; ring)
  rw [integral_prod_symm _ hI,integral_congr_ae hp,integral_neg,neg_add_cancel]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Every-time integrability and strong L1 continuity of the renormalized linear profile -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_renormalized_traces
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (β : Renormalization) :
    (∀ t ∈ Icc 0 T, Integrable (fun p : Phase =>
      linearRenormalizedDensity f G.weakLimit.kineticProfile β (t,p))) ∧
    ∀ t ∈ Icc 0 T, Tendsto (fun s => eLpNorm (fun p : Phase =>
      linearRenormalizedDensity f G.weakLimit.kineticProfile β (s,p)-
        linearRenormalizedDensity f G.weakLimit.kineticProfile β (t,p)) 1 volume)
      (𝓝[Icc 0 T] t) (𝓝 0) := by
  have hmm : Measurable (fun p : Phase => maxwellian p.2) := by unfold maxwellian; fun_prop
  have hfi : Integrable f := (show FiniteEntropyDatum f from
    ⟨ae_of_all _ hf,hfm.aestronglyMeasurable,hi⟩).integrable
  have hai := β.weighted_integrable hfm hmm hf (fun p => maxwellian_pos p.2) hfi
  have hri := G.linear_renormalized_source_integrable hf hi hT β
  apply Published.integrable_path_trace hT hai hri
  filter_upwards [G.linear_renormalized_integral_paths hf hi β] with p hp
  exact fun t ht => hp t ht.1

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong renormalized time traces in physical coordinates -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

def linearRenormalizedEvolution (f : Density) (F : (ℝ × Position) × Velocity → ℝ)
    (β : Renormalization) (t : ℝ) (p : Phase) : ℝ :=
  linearRenormalizedDensity f F β (t,TorusFlight.flight (-t) p)

theorem linearRenormalizedEvolution_initial (f : Density) (F : (ℝ × Position) × Velocity → ℝ)
    (β : Renormalization) (p : Phase) :
    linearRenormalizedEvolution f F β 0 p = maxwellian p.2*β.toFun (f p/maxwellian p.2) := by
  simp only [linearRenormalizedEvolution,neg_zero,TorusFlight.flight_zero,
    linearRenormalizedDensity,physicalLinearProfile_initial]

theorem GlobalCollisionLimit.linear_renormalized_eulerian_traces
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (β : Renormalization) :
    (∀ t ∈ Icc 0 T, Integrable (linearRenormalizedEvolution f G.weakLimit.kineticProfile β t)) ∧
    ∀ t ∈ Icc 0 T, Tendsto (fun s => eLpNorm (fun p : Phase =>
      linearRenormalizedEvolution f G.weakLimit.kineticProfile β s p-
        linearRenormalizedEvolution f G.weakLimit.kineticProfile β t p) 1 volume)
      (𝓝[Icc 0 T] t) (𝓝 0) := by
  obtain ⟨hI,hC⟩ := G.linear_renormalized_traces hf hi hT β
  refine ⟨fun t ht => (TorusFlight.flight_measurePreserving (-t)).integrable_comp_of_integrable (hI t ht),?_⟩
  intro t ht
  exact TorusFlight.strong_curve_flight hI ht (hC t ht)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Joint measurability of the actual linear characteristic profile -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem physicalLinearProfile_measurable {f : Density} (hfm : Measurable f)
    {F : (ℝ × Position) × Velocity → ℝ} (hFm : Measurable F) :
    Measurable (physicalLinearProfile f F) := by
  have hk := physicalCharacteristicFrequency_measurable hFm
  have hg := physicalCharacteristicGain_measurable hFm
  have hK := TransportPrimitive.measurable_interval_primitive hk
  have hA := TransportPrimitive.measurable_interval_primitive (hK.exp.mul hg)
  exact hK.neg.exp.mul ((hfm.comp measurable_snd).add hA)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Local unit-normalized gain integrability for the characteristic profile -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem GlobalCollisionLimit.linear_unit_gain_integrable
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Integrable (fun z : ℝ × Phase => physicalCharacteristicGain G.weakLimit.kineticProfile z /
      (1+max 0 (physicalLinearProfile f G.weakLimit.kineticProfile z)))
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) := by
  let U := physicalLinearProfile f G.weakLimit.kineticProfile
  let a := physicalCharacteristicGain G.weakLimit.kineticProfile
  let μ : Measure (ℝ × Phase) := (volume.restrict (Icc 0 T)).prod
    ((volume : Measure Position).prod ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))
  have hμ : μ ≤ (volume.restrict (Icc 0 T)).prod (volume : Measure Phase) := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod_mono le_rfl (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hbase := (G.linear_normalized_gain_integrable hf hi hT).mono_measure hμ
  have hUm := physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable
  have ham := physicalCharacteristicGain_measurable G.weakLimit.kineticProfile_measurable
  have ht : ∀ᵐ z ∂μ, z.1 ∈ Icc 0 T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  have hv : ∀ᵐ z ∂μ, z.2.2 ∈ Metric.closedBall (0:Velocity) R :=
    Measure.quasiMeasurePreserving_snd.ae
      (Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_closedBall))
  apply (hbase.const_mul (1+1/maxwellianLower R)).mono'
    (ham.div (measurable_const.add (measurable_const.max hUm))).aestronglyMeasurable
  filter_upwards [ht,hv] with z hzt hzv
  have hu : 0 ≤ U z := physicalLinearProfile_nonneg hf
    (fun _ => G.weakLimit.nonnegative _) hzt.1 z.2
  have ha : 0 ≤ a z := physicalCharacteristicGain_nonneg (fun _ => G.weakLimit.nonnegative _) z
  change ‖a z/(1+max 0 (U z))‖ ≤ (1+1/maxwellianLower R)*(a z/(1+U z/maxwellian z.2.2))
  rw [max_eq_right hu,Real.norm_eq_abs,abs_of_nonneg (div_nonneg ha (by positivity))]
  exact change_normalizer_bound ha hu (maxwellianLower_pos R)
    (maxwellianLower_le hR (by simpa only [Metric.mem_closedBall,dist_zero_right] using hzv))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Slice convergence of the actual characteristic profile -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_profile_slice_tendsto
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T)
    {s : ℕ → ℝ} (hs : ∀ n, s n ∈ Icc 0 T) (hst : Tendsto s atTop (𝓝 t)) :
    ∀ᵐ p ∂(volume : Measure Phase),
      Tendsto (fun n => physicalLinearProfile f G.weakLimit.kineticProfile (s n,p))
        atTop (𝓝 (physicalLinearProfile f G.weakLimit.kineticProfile (t,p))) := by
  filter_upwards [G.linear_profile_absolutelyContinuous hf hi] with p hp
  have hc : ContinuousOn (fun r => physicalLinearProfile f G.weakLimit.kineticProfile (r,p))
      (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using (hp T hT).continuousOn
  exact (hc.continuousWithinAt ht).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hst,Eventually.of_forall hs⟩)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
