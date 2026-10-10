import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveComparisonBound
import OAI.MathematicalPhysics.Boltzmann.Branching.InMeasureDifference
import OAI.MathematicalPhysics.Boltzmann.Branching.InitialLinearComparison
import OAI.MathematicalPhysics.Boltzmann.Compactness.L1VelocityTranslationApproximation
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicStrongAverages
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicCharacteristicGainUnit
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicDensityStrong
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalLinearContinuous
import OAI.MathematicalPhysics.Boltzmann.Compactness.PrefixComparisonConvergence
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusVelocityWindowAE

namespace OAI

section

/-! # The gain discrepancy against the actual linear characteristic profile -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem GlobalCollisionLimit.linear_gain_discrepancy_L1 {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    let I := fun n => G.weakLimit.indices (n+Nat.ceil T)
    let S := fun n => approximatingSolution f hfm (I n)
    let U := physicalLinearProfile f G.weakLimit.kineticProfile
    Tendsto (fun n => eLpNorm (fun z : ℝ × Phase =>
      ((S n).characteristicGain z-physicalCharacteristicGain G.weakLimit.kineticProfile z)/
        (1+(S n).density (z.1,TorusFlight.flight z.1 z.2)+max 0 (U z))) 1
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) atTop (𝓝 0) := by
  let ν : Measure Velocity := volume.restrict (Metric.closedBall 0 R)
  let : IsFiniteMeasure ν :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne
  let μ : Measure (ℝ × Phase) := (volume.restrict (Icc 0 T)).prod
    ((volume : Measure Position).prod ν)
  let I := fun n => G.weakLimit.indices (n+Nat.ceil T)
  let S := fun n => approximatingSolution f hfm (I n)
  let u n (z : ℝ × Phase) := (S n).density (z.1,TorusFlight.flight z.1 z.2)
  let v (z : ℝ × Phase) := max 0 (physicalLinearProfile f G.weakLimit.kineticProfile z)
  let a n := (S n).characteristicGain
  let b := physicalCharacteristicGain G.weakLimit.kineticProfile
  have hum n : Measurable (u n) := (S n).measurable.comp
    (measurable_fst.prodMk TorusFlight.measurable_flight)
  have hvm : Measurable v := measurable_const.max
    (physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable)
  have ham n : Measurable (a n) := (S n).characteristicGain_measurable
  have hbm : Measurable b := physicalCharacteristicGain_measurable G.weakLimit.kineticProfile_measurable
  have ha : TendstoInMeasure μ a atTop b := by
    have h := (G.gain_in_measure hf hi hT R).comp (tendsto_add_atTop_nat (Nat.ceil T))
    exact inMeasure_comp_measurePreserving
      (TorusFlight.alongRegroup_measurePreserving (volume.restrict (Icc 0 T)) ν)
      (fun n => gain_measurable _ (S n).kineticProfile_measurable)
      (CollisionCompactness.gainDensity_measurable G.weakLimit.kineticProfile_measurable) h
  have hb : TendstoInMeasure μ (fun _ : ℕ => b) atTop b := by
    intro ε hε
    simpa only [edist_self,not_le.mpr hε,Set.ofPred_false,measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ≥0∞)) atTop (𝓝 0))
  have hIc n : Nat.ceil T ≤ I n :=
    (Nat.le_add_left (Nat.ceil T) n).trans (G.weakLimit.increasing.id_le _)
  have hui : UniformIntegrable (fun n z => a n z/(1+u n z)) 1 μ := by
    exact characteristic_gain_unit_uniformIntegrable f hfm hf hi hT hR I hIc
  have hvi : UniformIntegrable (fun _ : ℕ => fun z => b z/(1+v z)) 1 μ :=
    uniformIntegrable_const (by norm_num) (by norm_num)
      (memLp_one_iff_integrable.mpr (G.linear_unit_gain_integrable hf hi hT hR))
  exact normalized_source_difference_L1 hum (fun _ => hvm) ham (fun _ => hbm)
    (fun n z => (S n).nonnegative _) (fun _ z => le_max_left _ _)
    (fun n z => (gain_bounds (by positivity) (S n).kineticProfile_measurable
      (fun _ => (S n).nonnegative _) _).1)
    (fun _ z => physicalCharacteristicGain_nonneg (fun _ => G.weakLimit.nonnegative _) z)
    ha hb hui hvi

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Comparing each positive approximation to the actual linear limit profile -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open TransportPrimitive

def linearComparisonError {N H : ℝ} {f₀ : Density}
    (S : BoundedCutoffSolution N H f₀) (f : Density)
    (F : (ℝ × Position) × Velocity → ℝ) (z : ℝ × Phase) : ℝ :=
  |(S.characteristicGain z-physicalCharacteristicGain F z)/
    (1+S.density (z.1,TorusFlight.flight z.1 z.2)+max 0 (physicalLinearProfile f F z))|+
  |S.characteristicLossDefect z/(1+S.density (z.1,TorusFlight.flight z.1 z.2))|+
  |physicalCharacteristicFrequency S.kineticProfile z-physicalCharacteristicFrequency F z|

theorem linearComparisonError_measurable {N H : ℝ} {f₀ f : Density}
    (S : BoundedCutoffSolution N H f₀) (hfm : Measurable f)
    {F : (ℝ × Position) × Velocity → ℝ} (hFm : Measurable F) :
    Measurable (linearComparisonError S f F) := by
  have hum := S.measurable.comp (measurable_fst.prodMk TorusFlight.measurable_flight)
  have hvm := (measurable_const (a := (0:ℝ))).max (physicalLinearProfile_measurable hfm hFm)
  exact ((((S.characteristicGain_measurable.sub (physicalCharacteristicGain_measurable hFm)).div
    ((measurable_const.add hum).add hvm)).abs).add
      ((S.characteristicLossDefect_measurable.div (measurable_const.add hum)).abs)).add
        (((physicalCharacteristicFrequency_measurable S.kineticProfile_measurable).sub
          (physicalCharacteristicFrequency_measurable hFm)).abs)

theorem linearComparisonError_nonneg {N H : ℝ} {f₀ : Density}
    (S : BoundedCutoffSolution N H f₀) (f : Density)
    (F : (ℝ × Position) × Velocity → ℝ) (z : ℝ × Phase) :
    0 ≤ linearComparisonError S f F z :=
  add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)

theorem GlobalCollisionLimit.positive_linear_comparison
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {N H : ℝ} {f₀ : Density} (S : BoundedCutoffSolution N H f₀) (hN : 0 < N) :
    ∀ᵐ p ∂(volume : Measure Phase), ∀ t ∈ Icc 0 H,
      |positiveDifference (S.density (t,TorusFlight.flight t p))
        (physicalLinearProfile f G.weakLimit.kineticProfile (t,p))| ≤
      |positiveDifference (f₀ p) (f p)|+
        ∫ r in 0..t, linearComparisonError S f G.weakLimit.kineticProfile (r,p) := by
  filter_upwards [G.flight_integrable_locally hf hi,
    G.linear_profile_absolutelyContinuous hf hi,G.linear_profile_hasDerivAt_ae hf hi]
    with p hp hac hd
  intro t ht
  let U := fun r => physicalLinearProfile f G.weakLimit.kineticProfile (r,p)
  have hs r (hr : r ∈ Icc 0 t) : S.dampedPath p r = S.density (r,TorusFlight.flight r p) :=
    S.dampedPath_eq ⟨hr.1,hr.2.trans ht.2⟩ p
  have hsu r (hr : r ∈ Icc 0 t) : 0 ≤ S.dampedPath p r := by rw [hs r hr]; exact S.nonnegative _
  have hu r (hr : r ∈ Icc 0 t) : 0 ≤ U r :=
    physicalLinearProfile_nonneg hf (fun _ => G.weakLimit.nonnegative _) hr.1 p
  have hgi := (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr (hp t ht.1).1
  have hki := (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr (hp t ht.1).2
  have hdu : ∀ᵐ r, r ∈ Icc 0 t → HasDerivAt U
      (physicalCharacteristicGain G.weakLimit.kineticProfile (r,p)-
        physicalCharacteristicFrequency G.weakLimit.kineticProfile (r,p)*U r+0) r := by
    simpa only [add_zero] using hd t ht.1
  have hh := positiveDifference_error_bound ht.1
    (S.dampedPath_absolutelyContinuous hN p t) (hac t ht.1) hsu hu
    (fun r _ => (gain_bounds hN S.kineticProfile_measurable (fun _ => S.nonnegative _) _).1)
    (fun r _ => physicalCharacteristicGain_nonneg (fun _ => G.weakLimit.nonnegative _) (r,p))
    (fun r _ => physicalCharacteristicFrequency_nonneg (fun _ => S.nonnegative _) (r,p))
    (fun r _ => physicalCharacteristicFrequency_nonneg (fun _ => G.weakLimit.nonnegative _) (r,p))
    (fun r _ => S.characteristicLossDefect_nonneg hN (r,p))
    (fun _ _ => le_refl 0)
    (S.gain_path_integrable hN p t) hgi (S.frequency_path_integrable hN.le p t) hki
    (S.lossDefect_path_integrable hN p t) intervalIntegrable_const
    (S.dampedPath_physical_derivative hN ht p) hdu
  rw [hs t ⟨ht.1,le_rfl⟩,S.dampedPath_initial,physicalLinearProfile_initial] at hh
  apply hh.trans_eq
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc 0 t := by simpa only [uIcc_of_le ht.1] using hr
  dsimp only [linearComparisonError]
  rw [hs r hr',max_eq_right (hu r hr'),abs_div,
    abs_of_pos (show 0 < 1+S.density (r,TorusFlight.flight r p)+U r by
      have := S.nonnegative (r,TorusFlight.flight r p); have := hu r hr'; positivity)]
  rw [abs_of_nonneg (div_nonneg (S.characteristicLossDefect_nonneg hN (r,p)) (by
    have := S.nonnegative (r,TorusFlight.flight r p); positivity))]
  simp only [zero_div,add_zero]
  rfl

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # All errors in the comparison with the linear limit profile vanish -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness

theorem GlobalCollisionLimit.characteristic_loss_residual_L1
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm (fun z : ℝ × Phase =>
      (approximatingSolution f hfm (G.weakLimit.indices n)).characteristicLossDefect z/
        (1+(approximatingSolution f hfm (G.weakLimit.indices n)).density
          (z.1,TorusFlight.flight z.1 z.2))) 1
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) atTop (𝓝 0) := by
  apply (G.loss_residual_L1 hf hi hT hR).congr'
  apply Eventually.of_forall
  intro n
  have hm := (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
  exact (eLpNorm_comp_measurePreserving
    (((lossDensity_measurable hm).sub (loss_measurable _ hm)).div
      (measurable_const.add hm)).aestronglyMeasurable
    (TorusFlight.alongRegroup_measurePreserving (volume.restrict (Icc 0 T))
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))).symm

theorem GlobalCollisionLimit.linear_comparison_error_L1
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm (linearComparisonError
      (approximatingSolution f hfm (G.weakLimit.indices (n+Nat.ceil T))) f G.weakLimit.kineticProfile)
      1 ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) atTop (𝓝 0) := by
  let I := fun n => G.weakLimit.indices (n+Nat.ceil T)
  let S := fun n => approximatingSolution f hfm (I n)
  let u n (z : ℝ × Phase) := (S n).density (z.1,TorusFlight.flight z.1 z.2)
  let v := fun z => max 0 (physicalLinearProfile f G.weakLimit.kineticProfile z)
  have hum n : Measurable (u n) := (S n).measurable.comp
    (measurable_fst.prodMk TorusFlight.measurable_flight)
  have hvm : Measurable v := measurable_const.max
    (physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable)
  have ha n := ((S n).characteristicGain_measurable.sub
    (physicalCharacteristicGain_measurable G.weakLimit.kineticProfile_measurable)).div
      (((measurable_const (a := (1:ℝ))).add (hum n)).add hvm)
  have hb n := (S n).characteristicLossDefect_measurable.div ((measurable_const (a := (1:ℝ))).add (hum n))
  have hc n := (physicalCharacteristicFrequency_measurable (S n).kineticProfile_measurable).sub
    (physicalCharacteristicFrequency_measurable G.weakLimit.kineticProfile_measurable)
  have ht := strongL1_abs_sum_four ha hb hc (fun _ => measurable_const (a := (0:ℝ)))
    (G.linear_gain_discrepancy_L1 hf hi hT hR)
    ((G.characteristic_loss_residual_L1 hf hi hT hR).comp (tendsto_add_atTop_nat (Nat.ceil T)))
    ((G.characteristic_frequency_strong hf hi hT hR).comp (tendsto_add_atTop_nat (Nat.ceil T)))
    (by simp)
  apply ht.congr'
  apply Eventually.of_forall
  intro n
  apply congrArg (fun g => eLpNorm g 1
    ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))))
  funext z
  simp only [abs_zero,add_zero,Pi.add_apply,Pi.div_apply,Pi.sub_apply]
  rfl

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The approximations approach the linear profile in the positive metric -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness TransportPrimitive

theorem GlobalCollisionLimit.linear_positive_difference_L1
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    let I := fun n => G.weakLimit.indices (n+Nat.ceil T)
    Tendsto (fun n => eLpNorm (fun z : ℝ × Phase => positiveDifference
      ((approximatingSolution f hfm (I n)).density (z.1,TorusFlight.flight z.1 z.2))
      (max 0 (physicalLinearProfile f G.weakLimit.kineticProfile z))) 1
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) atTop (𝓝 0) := by
  let I := fun n => G.weakLimit.indices (n+Nat.ceil T)
  let S := fun n => approximatingSolution f hfm (I n)
  let u n (z : ℝ × Phase) := (S n).density (z.1,TorusFlight.flight z.1 z.2)
  let v := fun z => max 0 (physicalLinearProfile f G.weakLimit.kineticProfile z)
  let E n := linearComparisonError (S n) f G.weakLimit.kineticProfile
  let d n (p : Phase) := |positiveDifference (initialApproximation ((I n:ℝ)+1) f p) (f p)|
  have hum n : Measurable (u n) := (S n).measurable.comp
    (measurable_fst.prodMk TorusFlight.measurable_flight)
  have hvm : Measurable v := measurable_const.max
    (physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable)
  have hdm n : Measurable (d n) :=
    (((initialApproximation_measurable _ hfm).sub hfm).div
      ((measurable_const.add (initialApproximation_measurable _ hfm)).add hfm)).abs
  have hν : (volume : Measure Position).prod
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)) ≤ (volume : Measure Phase) := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod_mono le_rfl Measure.restrict_le_self
  have hdt := initialApproximation_linear_comparison_L1 hfm hf
    (integrable_of_entropyGauge hfm hf hi)
    (G.weakLimit.increasing.tendsto_atTop.comp (tendsto_add_atTop_nat (Nat.ceil T))) hν
  apply prefixComparison_ae_strongL1 hT
    (fun n => ((hum n).sub hvm).div ((measurable_const.add (hum n)).add hvm))
    (fun n => linearComparisonError_measurable (S n) hfm G.weakLimit.kineticProfile_measurable)
    hdm (fun n z => linearComparisonError_nonneg (S n) f G.weakLimit.kineticProfile z)
    _ hdt (G.linear_comparison_error_L1 hf hi hT hR)
  intro n
  have hp := (G.positive_linear_comparison hf hi (S n) (by positivity)).filter_mono (ae_mono hν)
  filter_upwards [hp] with p hp
  intro t ht
  have hIc : Nat.ceil T ≤ I n :=
    (Nat.le_add_left (Nat.ceil T) n).trans (G.weakLimit.increasing.id_le _)
  have hIT : T ≤ (I n:ℝ)+1 := by
    have hc := Nat.le_ceil T
    have hn : (Nat.ceil T:ℝ) ≤ (I n:ℝ) := by exact_mod_cast hIc
    linarith
  have hv : 0 ≤ physicalLinearProfile f G.weakLimit.kineticProfile (t,p) :=
    physicalLinearProfile_nonneg hf (fun _ => G.weakLimit.nonnegative _) ht.1 p
  change |positiveDifference _ (max 0 (physicalLinearProfile f G.weakLimit.kineticProfile (t,p)))| ≤ _
  rw [max_eq_right hv]
  exact hp t ⟨ht.1,ht.2.trans hIT⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong approximation of the physical linear characteristic profile -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem GlobalCollisionLimit.linear_profile_approximation_L1
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    let I := fun n => G.weakLimit.indices (n+Nat.ceil T)
    Tendsto (fun n => eLpNorm (fun z : ℝ × Phase =>
      (approximatingSolution f hfm (I n)).density (z.1,TorusFlight.flight z.1 z.2)-
        max 0 (physicalLinearProfile f G.weakLimit.kineticProfile z)) 1
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) atTop (𝓝 0) := by
  let I := fun n => G.weakLimit.indices (n+Nat.ceil T)
  let S := fun n => approximatingSolution f hfm (I n)
  let u n (z : ℝ × Phase) := (S n).density (z.1,TorusFlight.flight z.1 z.2)
  let v := fun z => max 0 (physicalLinearProfile f G.weakLimit.kineticProfile z)
  let μ : Measure (ℝ × Phase) := (volume.restrict (Icc 0 T)).prod
    ((volume : Measure Position).prod ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))
  have hum n : Measurable (u n) := (S n).measurable.comp
    (measurable_fst.prodMk TorusFlight.measurable_flight)
  have hvm : Measurable v := measurable_const.max
    (physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable)
  have hbase := uniformIntegrable_restrict
    (uniformIntegrable_comp (approximatingSolution_compactness_hypotheses f hfm hf hi
      (volume.restrict (Icc 0 T))).1 I) (univ ×ˢ Metric.closedBall (0:Velocity) R)
  rw [← Measure.prod_restrict,Measure.restrict_univ] at hbase
  have hui0 := TorusFlight.uniformIntegrable_along_regroup_local
      (μ := volume.restrict (Icc 0 T))
      (ν := (volume : Measure Velocity).restrict (Metric.closedBall 0 R))
      (f := fun n => (S n).kineticProfile)
      (fun n => (S n).kineticProfile_measurable) hbase
  have he : (fun n => TorusFlight.along (TorusFlight.regroup (S n).kineticProfile)) = u := by
    funext n z
    rfl
  rw [he] at hui0
  have hui : UniformIntegrable u 1 μ := hui0
  have hμ : μ ≤ (volume.restrict (Icc 0 T)).prod (volume : Measure Phase) := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod_mono le_rfl (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hvInt : Integrable v μ := by
    apply ((G.linear_profile_integrable hf hi hT).mono_measure hμ).congr
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with z hz
    exact (max_eq_right (physicalLinearProfile_nonneg hf
      (fun _ => G.weakLimit.nonnegative _) hz.1 z.2)).symm
  have hvi : UniformIntegrable (fun _ : ℕ => v) 1 μ :=
    uniformIntegrable_const (by norm_num) (by norm_num) (memLp_one_iff_integrable.mpr hvInt)
  exact positiveDifference_L1 hum (fun _ => hvm)
    (fun n z => (S n).nonnegative _) (fun _ z => le_max_left _ _) hui hvi
    (G.linear_positive_difference_L1 hf hi hT hR)

theorem GlobalCollisionLimit.characteristic_density_strong
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm (fun z : ℝ × Phase =>
      (approximatingSolution f hfm (G.weakLimit.indices n)).density (z.1,TorusFlight.flight z.1 z.2)-
        G.weakLimit.density (z.1,TorusFlight.flight z.1 z.2)) 1
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) atTop (𝓝 0) := by
  have hh := TorusFlight.strong_along_regroup
    (μ := volume.restrict (Icc 0 T))
    (ν := (volume : Measure Velocity).restrict (Metric.closedBall 0 R))
    (f := fun n => (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)
    (g := G.weakLimit.kineticProfile)
    (fun n => (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable)
    G.weakLimit.kineticProfile_measurable (G.density_strong hf hi hT hR)
  apply hh.congr'
  exact Eventually.of_forall (fun n => rfl)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
