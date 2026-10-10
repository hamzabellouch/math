import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveComparisonBound
import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedVelocityIntegral
import OAI.MathematicalPhysics.Boltzmann.Branching.RightAverageBound
import OAI.MathematicalPhysics.Boltzmann.Branching.SmoothedPrePostIdentity
import OAI.MathematicalPhysics.Boltzmann.Branching.VariableSurvival
import OAI.MathematicalPhysics.Boltzmann.Collision.AngularPairTests
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyDissipationAverage
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalAdmissibility
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedPairCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicInitialEntropyLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicJointBudgetLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicMomentEntropy
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicRenormalizedCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicWeakCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalFrequencyWindow
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongCompactPairTests
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongPairMoment
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakConservedMarginal
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusVelocityWindowAE

namespace OAI

section

/-! # A real-valued joint entropy budget on each finite right interval -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem GlobalWeakLimit.entropy_path_integrable {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun t => relativeEntropy (fun p => G.density (t,p))) (volume.restrict (Icc 0 T)) := by
  convert (G.entropy_on_window hf hi hT).1.integral_prod_left using 1
  funext t
  apply integral_congr_ae
  exact ae_of_all _ (fun p => (scalarRelativeEntropy_eq (maxwellian_pos p.2) _).symm)

theorem GlobalWeakLimit.entropyMarginal_ae_eq {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    entropyMarginal G.density =ᵐ[volume] fun t => ENNReal.ofReal (relativeEntropy (fun p => G.density (t,p))) := by
  filter_upwards [G.finiteEntropy_ae_volume hf hi] with t ht
  exact entropyMarginal_eq G.measurable G.nonnegative t ht.1.2.2

theorem GlobalCollisionLimit.real_joint_interval_budget {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    (∫ t in r..R, relativeEntropy (fun p => G.weakLimit.density (t,p)))+
      (R-r)*(rateDissipation ((volume.restrict (Icc 0 r)).prod (volume : Measure Position))
        G.weakLimit.kineticProfile).toReal ≤ (R-r)*relativeEntropy f := by
  let H t := relativeEntropy (fun p => G.weakLimit.density (t,p))
  let d := rateDissipation ((volume.restrict (Icc 0 r)).prod (volume : Measure Position)) G.weakLimit.kineticProfile
  have hR : 0 ≤ R := hr.trans hrR
  have hI : Integrable H (volume.restrict (Icc r R)) :=
    (G.weakLimit.entropy_path_integrable hf hi hR).mono_measure
      (Measure.restrict_mono (Icc_subset_Icc hr le_rfl) le_rfl)
  have hn : 0 ≤ᵐ[volume.restrict (Icc r R)] H := by
    filter_upwards [ae_restrict_of_ae (G.weakLimit.finiteEntropy_ae_volume hf hi)] with t ht
    exact relativeEntropy_nonneg ht.1
  have hval : (∫⁻ t in Icc r R, entropyMarginal G.weakLimit.density t) =
      ENNReal.ofReal (∫ t in r..R, H t) := by
    rw [lintegral_congr_ae (ae_restrict_of_ae (G.weakLimit.entropyMarginal_ae_eq hf hi)),
      ← ofReal_integral_eq_lintegral_ofReal hI hn,
      integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hrR]
  have hd : d ≠ ⊤ := ne_of_lt ((G.dissipation_bound hf hi hr).trans_lt ENNReal.ofReal_lt_top)
  have hb := G.averaged_joint_budget hf hi hr hrR measurableSet_Icc (Subset.rfl : Icc r R ⊆ Icc r R)
  rw [hval,Real.volume_Icc] at hb
  change ENNReal.ofReal (∫ t in r..R, H t)+ENNReal.ofReal (R-r)*d ≤
    ENNReal.ofReal (R-r)*ENNReal.ofReal (relativeEntropy f) at hb
  rw [← ENNReal.ofReal_toReal hd] at hb
  have hdiff : 0 ≤ R-r := sub_nonneg.mpr hrR
  have hInt : 0 ≤ ∫ t in r..R, H t := by
    rw [intervalIntegral.integral_of_le hrR,← integral_Icc_eq_integral_Ioc]
    exact integral_nonneg_of_ae hn
  have h0 := relativeEntropy_nonneg (show FiniteEntropyDatum f from ⟨ae_of_all _ hf,hfm.aestronglyMeasurable,hi⟩)
  rw [← ENNReal.ofReal_mul hdiff,← ENNReal.ofReal_mul hdiff,
    ← ENNReal.ofReal_add hInt (mul_nonneg hdiff ENNReal.toReal_nonneg)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hdiff h0)).mp hb

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong bounded velocity averages for the actual global collision limit -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness

theorem GlobalCollisionLimit.velocity_average_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) {ψ : Velocity → ℝ} (hψ : Measurable ψ)
    (C : ℝ≥0) (hC : ∀ v, |ψ v| ≤ C) :
    Tendsto (fun n => eLpNorm (fun z =>
      (∫ v, ψ v*(approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (z,v))-
      (∫ v, ψ v*G.weakLimit.kineticProfile (z,v)))
      1 ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let F n := (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile
  let K := (volume.restrict (Icc 0 T)).real univ*approximationEntropyBudget f
  have hFm n : Measurable (F n) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
  have hFn n p : 0 ≤ F n p :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _
  have hEi n : Integrable (entropyGauge (F n)) (μ.prod volume) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integrable
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  have hEb n : (∫ p, entropyGauge (F n) p ∂μ.prod volume) ≤ K :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integral_le
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  have hFi n : Integrable (F n) (μ.prod volume) :=
    integrable_of_entropyGauge (hFm n) (hFn n) (hEi n)
  have hFb n : (∫ p, F n p ∂μ.prod volume) ≤ K :=
    (integral_mono (hFi n) (hEi n) (entropyGauge_ge_density (hFn n))).trans (hEb n)
  have hB : 0 < μ.real univ+|K|+1 := by positivity
  have hbound n : (∫ z, 1+fiberMass volume (F n) z ∂μ) ≤ μ.real univ+|K|+1 := by
    unfold fiberMass
    rw [integral_add (integrable_const 1) (hFi n).integral_prod_left, integral_const]
    simp only [smul_eq_mul,mul_one]
    rw [← integral_prod _ (hFi n)]
    linarith [hFb n,le_abs_self K]
  exact strong_average_of_normalized_pairs (G.weakLimit.kinetic_weak_on_window hT)
    (G.normalized_pairs T hT) hFm hFn (fun p => G.weakLimit.nonnegative _)
    hFi (G.mass_strong T hT) hB hbound hψ C hC

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Joint bounded-kernel convergence for the actual periodic approximations -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem GlobalCollisionLimit.bounded_kernel_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) {Z : Type*} [MeasurableSpace Z]
    (τ : Measure Z) [IsFiniteMeasure τ] {k : Z × Velocity → ℝ}
    (hk : Measurable k) (C : ℝ≥0) (hC : ∀ p, |k p| ≤ C) :
    Tendsto (fun n => eLpNorm (fun p : (ℝ × Position) × Z =>
      (∫ v, k (p.2,v)*(approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (p.1,v))-
      (∫ v, k (p.2,v)*G.weakLimit.kineticProfile (p.1,v)))
      1 (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod τ)) atTop (𝓝 0) := by
  have hw := G.weakLimit.kinetic_weak_on_window hT
  have hUi := (approximatingSolution_compactness_hypotheses f hfm hf hi
    (volume.restrict (Icc 0 T))).1
  obtain ⟨B,hB⟩ := hUi.2
  apply strong_bounded_kernel_averages
    (fun n => (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable)
    G.weakLimit.kineticProfile_measurable
    (fun n => memLp_one_iff_integrable.mp (hUi.memLp (G.weakLimit.indices n)))
    hw.2.1 (B := B) ENNReal.coe_ne_top (fun n => hB _) hk hC
  intro z
  exact G.velocity_average_strong hf hi hT
    (hk.comp (measurable_const.prodMk measurable_id)) C (fun v => hC (z,v))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Actual strong kernel averages with linear growth in incoming velocity -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem GlobalCollisionLimit.linear_kernel_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) {Z : Type*} [MeasurableSpace Z]
    (τ : Measure Z) [IsFiniteMeasure τ] {k : Z × Velocity → ℝ}
    (hk : Measurable k) (D : ℝ≥0) (hD : ∀ p, |k p| ≤ D*(1+‖p.2‖)) :
    Tendsto (fun n => eLpNorm (fun p : (ℝ × Position) × Z =>
      (∫ v, k (p.2,v)*(approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (p.1,v))-
      (∫ v, k (p.2,v)*G.weakLimit.kineticProfile (p.1,v)))
      1 (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod τ)) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let F n := (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile
  let g := G.weakLimit.kineticProfile
  let K := (volume.restrict (Icc 0 T)).real univ*approximationEntropyBudget f
  let C := max K (∫ p, entropyGauge g p ∂μ.prod volume)
  have hFm n : Measurable (F n) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
  have hFn n p : 0 ≤ F n p :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _
  have hEi n : Integrable (entropyGauge (F n)) (μ.prod volume) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integrable
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  have hEb n : (∫ p, entropyGauge (F n) p ∂μ.prod volume) ≤ C := by
    apply le_trans _ (le_max_left _ _)
    exact (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integral_le
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  have hgm : Measurable g := G.weakLimit.kineticProfile_measurable
  have hgn p : 0 ≤ g p := G.weakLimit.nonnegative _
  have hgi : Integrable (entropyGauge g) (μ.prod volume) := G.weakLimit.kinetic_entropy_on_window hf hi hT
  let b : Z × Velocity → ℝ := fun p => k p/(1+‖p.2‖)
  have hbm : Measurable b := hk.div (measurable_const.add measurable_snd.norm)
  have hb p : |b p| ≤ D := by
    rw [show b p = k p/(1+‖p.2‖) from rfl,abs_div,abs_of_pos (by positivity : 0 < 1+‖p.2‖)]
    exact (div_le_iff₀ (by positivity : 0 < 1+‖p.2‖)).mpr (hD p)
  have he (u : (ℝ × Position) × Velocity → ℝ) (p : (ℝ × Position) × Z) :
      (∫ v, b (p.2,v)*linearMoment u (p.1,v)) = ∫ v, k (p.2,v)*u (p.1,v) := by
    apply integral_congr_ae
    apply ae_of_all
    intro v
    dsimp only [b,linearMoment]
    field_simp [show (1+‖v‖:ℝ) ≠ 0 by positivity]
  obtain ⟨B,hB⟩ := (linearMoment_uniformIntegrable hFm hFn hEi hEb).2
  have h := strong_bounded_kernel_averages (fun n => linearMoment_measurable (hFm n))
    (linearMoment_measurable hgm) (fun n => linearMoment_integrable (hFm n) (hFn n) (hEi n))
    (linearMoment_integrable hgm hgn hgi) (B := B) ENNReal.coe_ne_top hB hbm hb
    (fun z => strong_linearMoment_averages hFm hFn hEi hEb hgm hgn hgi (le_max_right _ _)
      (fun ψ hψ E hE => G.velocity_average_strong hf hi hT hψ E hE)
      (hbm.comp (measurable_const.prodMk measurable_id)) D (fun v => hb (z,v)))
    (τ := τ)
  simpa only [he] using h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Local strong convergence of the actual physical loss frequencies -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness

theorem GlobalCollisionLimit.frequency_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm (fun p =>
      kineticFrequency (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile p-
      kineticFrequency G.weakLimit.kineticProfile p)
      1 (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let τ : Measure Velocity := volume.restrict (Metric.closedBall 0 R)
  let : IsFiniteMeasure τ := isFiniteMeasure_restrict.mpr (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne
  let k : Velocity × Velocity → ℝ := fun p => min ‖p.1-p.2‖ (R+‖p.2‖)
  have hk : Measurable k := by dsimp only [k]; fun_prop
  have hb p : |k p| ≤ (R+1)*(1+‖p.2‖) := by
    rw [abs_of_nonneg (le_min (norm_nonneg _) (by positivity))]
    exact (min_le_right _ _).trans (by nlinarith [norm_nonneg p.2])
  have hs := G.linear_kernel_strong hf hi hT τ hk ⟨R+1,by positivity⟩ hb
  have hscaled := ENNReal.Tendsto.const_mul (a := ‖(2*Real.pi:ℝ)‖ₑ) hs
    (Or.inr (by rw [enorm_mul]; exact ENNReal.mul_ne_top (by simp) (by simp)))
  simp only [← eLpNorm_const_smul,Pi.smul_def,smul_eq_mul,mul_zero] at hscaled
  apply hscaled.congr'
  apply Eventually.of_forall
  intro n
  apply eLpNorm_congr_ae
  have hva : ∀ᵐ p ∂μ.prod τ, ‖p.2‖ ≤ R := by
    have hmem : ∀ᵐ v ∂τ, v ∈ Metric.closedBall (0:Velocity) R :=
      ae_restrict_mem Metric.isClosed_closedBall.measurableSet
    have h := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := τ)).ae hmem
    simpa only [Metric.mem_closedBall,dist_zero_right] using h
  filter_upwards [hva] with p hp
  have he (u : (ℝ × Position) × Velocity → ℝ) :
      (∫ v, k (p.2,v)*u (p.1,v)) = ∫ v, ‖p.2-v‖*u (p.1,v) := by
    apply integral_congr_ae
    apply ae_of_all
    intro v
    dsimp only [k]
    rw [min_eq_left ((norm_sub_le _ _).trans (add_le_add hp le_rfl))]
  simp only [he,kineticFrequency]
  ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The sharp joint entropy and physical dissipation bound for the same global limit -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem GlobalCollisionLimit.sharp_joint_entropy_dissipation
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ t ∂volume, 0 ≤ t →
      ENNReal.ofReal (relativeEntropy (fun p => G.weakLimit.density (t,p)))+
        rateDissipation ((volume.restrict (Icc 0 t)).prod (volume : Measure Position))
          G.weakLimit.kineticProfile ≤ ENNReal.ofReal (relativeEntropy f) := by
  let H t := relativeEntropy (fun p => G.weakLimit.density (t,p))
  let D t := rateDissipation ((volume.restrict (Icc 0 t)).prod (volume : Measure Position)) G.weakLimit.kineticProfile
  have hlocal (n : ℕ) : ∀ᵐ t ∂volume, t ∈ Ico 0 (n:ℝ) → H t+(D t).toReal ≤ relativeEntropy f := by
    apply ae_bound_of_right_integral_bound (Nat.cast_nonneg n)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le (Nat.cast_nonneg n)).mpr
        (G.weakLimit.entropy_path_integrable hf hi (Nat.cast_nonneg n)))
    intro t s ht hts _hs
    exact G.real_joint_interval_budget hf hi ht hts.le
  have hall : ∀ᵐ t ∂volume, ∀ n : ℕ, t ∈ Ico 0 (n:ℝ) → H t+(D t).toReal ≤ relativeEntropy f :=
    ae_all_iff.mpr hlocal
  filter_upwards [hall,G.weakLimit.finiteEntropy_ae_volume hf hi] with t ht hdata
  intro ht0
  obtain ⟨n,hn⟩ := exists_nat_gt t
  have hreal := ht n ⟨ht0,hn⟩
  have hd : D t ≠ ⊤ := ne_of_lt ((G.dissipation_bound hf hi ht0).trans_lt ENNReal.ofReal_lt_top)
  have hH : 0 ≤ H t := relativeEntropy_nonneg hdata.1
  change ENNReal.ofReal (H t)+D t ≤ _
  rw [← ENNReal.ofReal_toReal hd,← ENNReal.ofReal_add hH ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal hreal

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Actual physical frequencies and survival along torus characteristics -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

def physicalCharacteristicFrequency (f : (ℝ × Position) × Velocity → ℝ) : ℝ × Phase → ℝ :=
  TorusFlight.along (TorusFlight.regroup (kineticFrequency f))

def physicalCharacteristicPrimitive (T : ℝ) (f : (ℝ × Position) × Velocity → ℝ) :=
  Published.timePrimitive (volume.restrict (Icc 0 T)) (physicalCharacteristicFrequency f)

def physicalCharacteristicSurvival (T : ℝ) (f : (ℝ × Position) × Velocity → ℝ) :=
  Published.timeSurvival (volume.restrict (Icc 0 T)) (physicalCharacteristicFrequency f)

theorem physicalCharacteristicFrequency_measurable {f : (ℝ × Position) × Velocity → ℝ}
    (hf : Measurable f) : Measurable (physicalCharacteristicFrequency f) :=
  (kineticFrequency_measurable hf).comp
    ((measurable_fst.prodMk TorusFlight.measurable_flight.fst).prodMk measurable_snd.snd)

theorem physicalCharacteristicFrequency_nonneg {f : (ℝ × Position) × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : ℝ × Phase) : 0 ≤ physicalCharacteristicFrequency f z :=
  kineticFrequency_nonneg hf _

theorem physicalCharacteristicFrequency_integrable {f : (ℝ × Position) × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) {μ : Measure ℝ} [SFinite μ]
    (hi : Integrable (linearMoment f) ((μ.prod (volume : Measure Position)).prod volume))
    {R : ℝ} (hR : 0 ≤ R) :
    Integrable (physicalCharacteristicFrequency f)
      (μ.prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) :=
  (TorusFlight.alongRegroup_measurePreserving μ _).integrable_comp_of_integrable
    (kineticFrequency_integrable_local hfm hf hi hR)

theorem GlobalCollisionLimit.characteristic_frequency_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm
      (physicalCharacteristicFrequency (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile-
        physicalCharacteristicFrequency G.weakLimit.kineticProfile)
      1 ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) atTop (𝓝 0) :=
  TorusFlight.strong_along_regroup
    (fun n => kineticFrequency_measurable
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable)
    (kineticFrequency_measurable G.weakLimit.kineticProfile_measurable)
    (G.frequency_strong hf hi hT hR)

theorem GlobalCollisionLimit.characteristic_frequency_integrable {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    (∀ n, Integrable
      (physicalCharacteristicFrequency (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) ∧
    Integrable (physicalCharacteristicFrequency G.weakLimit.kineticProfile)
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) := by
  constructor
  · intro n
    apply physicalCharacteristicFrequency_integrable
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
      (fun p => (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _) _ hR
    exact linearMoment_integrable
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
      (fun p => (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _)
      ((approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integrable
        (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _))
  · exact physicalCharacteristicFrequency_integrable G.weakLimit.kineticProfile_measurable
      (fun _ => G.weakLimit.nonnegative _) (linearMoment_integrable G.weakLimit.kineticProfile_measurable
        (fun _ => G.weakLimit.nonnegative _) (G.weakLimit.kinetic_entropy_on_window hf hi hT)) hR

theorem GlobalCollisionLimit.characteristic_primitive_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm
      (physicalCharacteristicPrimitive T (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile-
        physicalCharacteristicPrimitive T G.weakLimit.kineticProfile)
      1 ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) atTop (𝓝 0) := by
  obtain ⟨hFi,hgi⟩ := G.characteristic_frequency_integrable hf hi hT hR
  exact Published.strong_timePrimitive
    (fun n => physicalCharacteristicFrequency_measurable
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable)
    (physicalCharacteristicFrequency_measurable G.weakLimit.kineticProfile_measurable)
    hFi hgi (G.characteristic_frequency_strong hf hi hT hR)

theorem GlobalCollisionLimit.characteristic_survival_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm
      (physicalCharacteristicSurvival T (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile-
        physicalCharacteristicSurvival T G.weakLimit.kineticProfile)
      1 ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) atTop (𝓝 0) := by
  obtain ⟨hFi,hgi⟩ := G.characteristic_frequency_integrable hf hi hT hR
  exact Published.strong_timeSurvival
    (fun n => physicalCharacteristicFrequency_measurable
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable)
    (physicalCharacteristicFrequency_measurable G.weakLimit.kineticProfile_measurable) hFi hgi
    (fun n => physicalCharacteristicFrequency_nonneg
      (fun q => (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative (q.1.1,(q.1.2,q.2))))
    (physicalCharacteristicFrequency_nonneg
      (fun q => G.weakLimit.nonnegative (q.1.1,(q.1.2,q.2))))
    (G.characteristic_frequency_strong hf hi hT hR)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The physical loss controls every supported approximation -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.velocity_fiber_moments (S : BoundedCutoffSolution N T f₀)
    (hN : 0 ≤ N) (t : ℝ) (x : Position) :
    Integrable (fun v => S.density (t,(x,v))) ∧
      Integrable (fun v => ‖v‖*S.density (t,(x,v))) := by
  obtain ⟨B,hB⟩ := S.bounded
  have hB0 : 0 ≤ B := (S.nonnegative (0,0)).trans (hB (0,0))
  have hm : Measurable (fun v => S.density (t,(x,v))) :=
    S.measurable.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hb v : |S.density (t,(x,v))| ≤ B :=
    (abs_of_nonneg (S.nonnegative _)).trans_le (hB _)
  exact ⟨bounded_velocity_fiber_integrable hm hb (fun v => S.support (t,(x,v))),
    bounded_velocity_fiber_weighted hB0 hN hm measurable_id.norm hb
      (fun v => S.support (t,(x,v))) (fun v hv => by simpa only [abs_norm] using hv)⟩

theorem BoundedCutoffSolution.loss_le_frequency (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (z : ℝ × Phase) :
    loss N (fun p => S.density (z.1,p)) z.2 ≤
      S.density z*kineticFrequency S.kineticProfile ((z.1,z.2.1),z.2.2) := by
  have hm : Measurable (fun p => S.density (z.1,p)) :=
    S.measurable.comp (measurable_const.prodMk measurable_id)
  obtain ⟨hi0,hi1⟩ := S.velocity_fiber_moments hN.le z.1 z.2.1
  have hi := integrable_loss_of_moments (fun p => S.density (z.1,p)) z.2.1 z.2.2 hi0 hi1
  have he := lossDensity_eq_mul_kineticFrequency (fun p => S.density (z.1,p)) z.2 hi
  exact (loss_le_physical hN hm (fun p => S.nonnegative _) z.2 hi0 hi1).trans_eq he

theorem BoundedCutoffSolution.frequency_bounded (S : BoundedCutoffSolution N T f₀)
    (hN : 0 ≤ N) (v : Velocity) :
    ∃ C : ℝ, ∀ t x, |kineticFrequency S.kineticProfile ((t,x),v)| ≤ C := by
  obtain ⟨B,hB⟩ := S.bounded
  let b : Velocity → ℝ := (Metric.closedBall 0 N).indicator (fun _ => (‖v‖+N)*B)
  have hi : Integrable b :=
    (integrableOn_const (isCompact_closedBall (0 : Velocity) N).measure_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  refine ⟨2*Real.pi*(∫ w, b w),?_⟩
  intro t x
  have hb w : ‖‖v-w‖*S.density (t,(x,w))‖ ≤ b w := by
    by_cases hw : w ∈ Metric.closedBall 0 N
    · have hwN : ‖w‖ ≤ N := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (S.nonnegative _))]
      change _ ≤ (Metric.closedBall 0 N).indicator (fun _ => (‖v‖+N)*B) w
      rw [indicator_of_mem hw]
      exact mul_le_mul ((norm_sub_le v w).trans (add_le_add le_rfl hwN)) (hB _)
        (S.nonnegative _) (add_nonneg (norm_nonneg _) hN)
    · have hwN : N < ‖w‖ := by
        simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hw
      change _ ≤ (Metric.closedBall 0 N).indicator (fun _ => (‖v‖+N)*B) w
      rw [S.support (t,(x,w)) hwN,mul_zero,norm_zero,indicator_of_notMem hw]
  have hh := norm_integral_le_of_norm_le hi (ae_of_all _ hb)
  change |2*Real.pi*(∫ w, ‖v-w‖*S.density (t,(x,w)))| ≤ _
  rw [abs_mul,abs_of_nonneg (show 0 ≤ 2*Real.pi by positivity)]
  exact mul_le_mul_of_nonneg_left hh (by positivity)

theorem BoundedCutoffSolution.frequency_path_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 ≤ N) (p : Phase) (t : ℝ) :
    IntervalIntegrable (fun r => physicalCharacteristicFrequency S.kineticProfile (r,p))
      volume 0 t := by
  obtain ⟨C,hC⟩ := S.frequency_bounded hN p.2
  apply (intervalIntegrable_const (c := C)).mono_fun'
  · exact ((physicalCharacteristicFrequency_measurable S.kineticProfile_measurable).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · exact ae_of_all _ (fun r => by
      change |kineticFrequency S.kineticProfile ((r,(TorusFlight.flight r p).1),p.2)| ≤ C
      exact hC r (TorusFlight.flight r p).1)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The supported approximants dominate their physical positive characteristic source -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {N T : ℝ} {f₀ : Density}

def BoundedCutoffSolution.characteristicGain (S : BoundedCutoffSolution N T f₀) : ℝ × Phase → ℝ :=
  TorusFlight.along (TorusFlight.regroup (gain N S.kineticProfile))

theorem BoundedCutoffSolution.characteristicGain_measurable (S : BoundedCutoffSolution N T f₀) :
    Measurable S.characteristicGain :=
  (gain_measurable N S.kineticProfile_measurable).comp
    ((measurable_fst.prodMk TorusFlight.measurable_flight.fst).prodMk measurable_snd.snd)

theorem BoundedCutoffSolution.gain_path_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (p : Phase) (t : ℝ) :
    IntervalIntegrable (fun r => S.characteristicGain (r,p)) volume 0 t := by
  apply (intervalIntegrable_const (c := gainBound N)).mono_fun'
  · exact (S.characteristicGain_measurable.comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [] with r
    have hb := gain_bounds hN S.kineticProfile_measurable
      (fun q => S.nonnegative _) ((r,(TorusFlight.flight r p).1),p.2)
    exact (Real.norm_of_nonneg hb.1).trans_le hb.2

theorem BoundedCutoffSolution.positive_physical_survival (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc 0 T) (p : Phase) :
    physicalCharacteristicSurvival t S.kineticProfile (t,p)*f₀ p +
      (∫ s in 0..t, Published.twoTimeSurvival (volume.restrict (Icc 0 t))
        (physicalCharacteristicFrequency S.kineticProfile) ((t,p),s)*
          S.characteristicGain (s,p)) ≤ S.density (t,TorusFlight.flight t p) := by
  let u := TransportPrimitive.damped (lossBound N) (f₀ p)
    (fun r => S.source (r,TorusFlight.flight r p))
  let k : ℝ → ℝ := fun r => physicalCharacteristicFrequency S.kineticProfile (r,p)
  let g : ℝ → ℝ := fun r => S.characteristicGain (r,p)
  have hs := S.source_path_integrable hN p t
  have hk : IntervalIntegrable k volume 0 t := S.frequency_path_integrable hN.le p t
  have hg : IntervalIntegrable g volume 0 t := S.gain_path_integrable hN p t
  have hu : AbsolutelyContinuousOnInterval u 0 t :=
    TransportPrimitive.damped_absolutelyContinuous hs
  have hd : ∀ᵐ r, r ∈ Icc 0 t → HasDerivAt u
      (S.source (r,TorusFlight.flight r p)-lossBound N*u r) r := by
    simpa only [uIcc_of_le ht.1] using TransportPrimitive.damped_derivative_ae hs
  have hb : ∀ᵐ r, r ∈ Icc 0 t → g r-k r*u r ≤
      S.source (r,TorusFlight.flight r p)-lossBound N*u r := by
    filter_upwards [] with r hr
    have hrT : r ∈ Icc 0 T := ⟨hr.1,hr.2.trans ht.2⟩
    have he : u r = S.density (r,TorusFlight.flight r p) := (S.along_eq_damped hrT p).symm
    rw [he]
    have hl := S.loss_le_frequency hN (r,TorusFlight.flight r p)
    change loss N (fun q => S.density (r,q)) (TorusFlight.flight r p) ≤
      S.density (r,TorusFlight.flight r p)*
        kineticFrequency S.kineticProfile ((r,(TorusFlight.flight r p).1),p.2) at hl
    change gain N (fun q => S.density (r,q)) (TorusFlight.flight r p)-
      kineticFrequency S.kineticProfile ((r,(TorusFlight.flight r p).1),p.2)*
        S.density (r,TorusFlight.flight r p) ≤ _
    dsimp only [BoundedCutoffSolution.source,positiveSource]
    nlinarith only [hl]
  have h := TransportPrimitive.variable_survival_with_source ht.1 hu hk hg hd hb
  have h0 : u 0 = f₀ p := by simp [u,TransportPrimitive.damped]
  have hut : u t = S.density (t,TorusFlight.flight t p) := (S.along_eq_damped ht p).symm
  rw [h0,hut] at h
  have he0 : physicalCharacteristicSurvival t S.kineticProfile (t,p) =
      Real.exp (-(∫ r in 0..t, k r)) := by
    unfold physicalCharacteristicSurvival Published.timeSurvival
    rw [Published.timePrimitive_eq_interval ⟨ht.1,le_rfl⟩]
  rw [he0]
  convert h using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs0
  have hs1 : s ∈ Icc 0 t := by simpa only [uIcc_of_le ht.1] using hs0
  dsimp only
  rw [Published.twoTimeSurvival_eq_interval
    (f := physicalCharacteristicFrequency S.kineticProfile) ⟨ht.1,le_rfl⟩ hs1
    (physicalCharacteristicFrequency_nonneg (f := S.kineticProfile)
      (fun q => S.nonnegative (q.1.1,(q.1.2,q.2)))) p hk]
  have h0s : IntervalIntegrable k volume 0 s := by
    apply hk.mono_set
    rw [uIcc_of_le hs1.1,uIcc_of_le ht.1]
    exact fun _ hr => ⟨hr.1,hr.2.trans hs1.2⟩
  have hst : IntervalIntegrable k volume s t := by
    apply hk.mono_set
    rw [uIcc_of_le hs1.2,uIcc_of_le ht.1]
    exact fun _ hr => ⟨hs1.1.trans hr.1,hr.2⟩
  have ha := intervalIntegral.integral_add_adjacent_intervals h0s hst
  have he : (∫ r in s..t, k r) = (∫ r in 0..t, k r)-(∫ r in 0..s, k r) := by linarith
  rw [show (∫ r in s..t, physicalCharacteristicFrequency S.kineticProfile (r,p)) =
    (∫ r in 0..t, k r)-(∫ r in 0..s, k r) from he]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The physical loss defect along each actual bounded characteristic -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {N T : ℝ} {f₀ : Density}

def BoundedCutoffSolution.characteristicLossDefect (S : BoundedCutoffSolution N T f₀) :
    ℝ × Phase → ℝ :=
  TorusFlight.along (TorusFlight.regroup
    (fun p => lossDensity S.kineticProfile p-loss N S.kineticProfile p))

theorem BoundedCutoffSolution.characteristicLossDefect_measurable
    (S : BoundedCutoffSolution N T f₀) : Measurable S.characteristicLossDefect :=
  ((lossDensity_measurable S.kineticProfile_measurable).sub
    (loss_measurable N S.kineticProfile_measurable)).comp
      ((measurable_fst.prodMk TorusFlight.measurable_flight.fst).prodMk measurable_snd.snd)

theorem BoundedCutoffSolution.physical_loss_eq (S : BoundedCutoffSolution N T f₀)
    (hN : 0 ≤ N) (z : (ℝ × Position) × Velocity) :
    lossDensity S.kineticProfile z = S.kineticProfile z*kineticFrequency S.kineticProfile z := by
  obtain ⟨h0,h1⟩ := S.velocity_fiber_moments hN z.1.1 z.1.2
  exact lossDensity_eq_mul_kineticFrequency _ z
    (integrable_loss_of_moments (fun q : Phase => S.density (z.1.1,q)) z.1.2 z.2 h0 h1)

theorem BoundedCutoffSolution.characteristicLossDefect_eq (S : BoundedCutoffSolution N T f₀)
    (hN : 0 ≤ N) (z : ℝ × Phase) :
    S.characteristicLossDefect z =
      S.density (z.1,TorusFlight.flight z.1 z.2)*physicalCharacteristicFrequency S.kineticProfile z-
        loss N (fun q => S.density (z.1,q)) (TorusFlight.flight z.1 z.2) := by
  change lossDensity S.kineticProfile ((z.1,(TorusFlight.flight z.1 z.2).1),z.2.2)-_ = _
  rw [S.physical_loss_eq hN]
  rfl

theorem BoundedCutoffSolution.characteristicLossDefect_nonneg (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (z : ℝ × Phase) : 0 ≤ S.characteristicLossDefect z := by
  rw [S.characteristicLossDefect_eq hN.le]
  exact sub_nonneg.mpr (S.loss_le_frequency hN (z.1,TorusFlight.flight z.1 z.2))

theorem BoundedCutoffSolution.lossDefect_path_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (p : Phase) (t : ℝ) :
    IntervalIntegrable (fun r => S.characteristicLossDefect (r,p)) volume 0 t := by
  obtain ⟨B,hB⟩ := S.bounded
  have hB0 : 0 ≤ B := (S.nonnegative (0,0)).trans (hB (0,0))
  obtain ⟨C,hC⟩ := S.frequency_bounded hN.le p.2
  apply (intervalIntegrable_const (c := B*C)).mono_fun'
  · exact (S.characteristicLossDefect_measurable.comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [] with r
    rw [Real.norm_of_nonneg (S.characteristicLossDefect_nonneg hN (r,p)),
      S.characteristicLossDefect_eq hN.le]
    have hl := (loss_bounds hN
      (S.measurable.comp (measurable_const.prodMk measurable_id))
      (fun q => S.nonnegative (r,q)) (TorusFlight.flight r p)).1
    apply (sub_le_self _ hl).trans
    apply mul_le_mul (hB (r,TorusFlight.flight r p))
      ((le_abs_self _).trans (hC r (TorusFlight.flight r p).1))
      (physicalCharacteristicFrequency_nonneg (f := S.kineticProfile)
        (fun q => S.nonnegative _) (r,p)) hB0

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual damped path with its physical frequency and nonnegative loss defect -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {N T : ℝ} {f₀ : Density}

def BoundedCutoffSolution.dampedPath (S : BoundedCutoffSolution N T f₀) (p : Phase) : ℝ → ℝ :=
  TransportPrimitive.damped (lossBound N) (f₀ p)
    (fun r => S.source (r,TorusFlight.flight r p))

theorem BoundedCutoffSolution.dampedPath_eq (S : BoundedCutoffSolution N T f₀)
    {t : ℝ} (ht : t ∈ Icc 0 T) (p : Phase) :
    S.dampedPath p t = S.density (t,TorusFlight.flight t p) := (S.along_eq_damped ht p).symm

theorem BoundedCutoffSolution.dampedPath_initial (S : BoundedCutoffSolution N T f₀) (p : Phase) :
    S.dampedPath p 0 = f₀ p := by simp [dampedPath,TransportPrimitive.damped]

theorem BoundedCutoffSolution.dampedPath_absolutelyContinuous (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (p : Phase) (t : ℝ) :
    AbsolutelyContinuousOnInterval (S.dampedPath p) 0 t :=
  TransportPrimitive.damped_absolutelyContinuous (S.source_path_integrable hN p t)

theorem BoundedCutoffSolution.dampedPath_physical_derivative (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc 0 T) (p : Phase) :
    ∀ᵐ r, r ∈ Icc 0 t → HasDerivAt (S.dampedPath p)
      (S.characteristicGain (r,p)-physicalCharacteristicFrequency S.kineticProfile (r,p)*
        S.dampedPath p r+S.characteristicLossDefect (r,p)) r := by
  have hd := TransportPrimitive.damped_derivative_ae (S.source_path_integrable hN p t)
    (L := lossBound N) (c := f₀ p)
  filter_upwards [hd] with r hr hrt
  have hrr : r ∈ Icc 0 T := ⟨hrt.1,hrt.2.trans ht.2⟩
  have hv := S.dampedPath_eq hrr p
  have hder := hr (by simpa only [uIcc_of_le ht.1] using hrt)
  change HasDerivAt (S.dampedPath p)
    (S.source (r,TorusFlight.flight r p)-lossBound N*S.dampedPath p r) r at hder
  have he : S.source (r,TorusFlight.flight r p)-lossBound N*S.dampedPath p r =
      S.characteristicGain (r,p)-physicalCharacteristicFrequency S.kineticProfile (r,p)*
        S.dampedPath p r+S.characteristicLossDefect (r,p) := by
    rw [S.characteristicLossDefect_eq hN.le,hv]
    change positiveSource N (fun q => S.density (r,q)) (TorusFlight.flight r p)-
        lossBound N*S.density (r,TorusFlight.flight r p) =
      gain N (fun q => S.density (r,q)) (TorusFlight.flight r p)-
        physicalCharacteristicFrequency S.kineticProfile (r,p)*S.density (r,TorusFlight.flight r p)+
        (S.density (r,TorusFlight.flight r p)*physicalCharacteristicFrequency S.kineticProfile (r,p)-
          loss N (fun q => S.density (r,q)) (TorusFlight.flight r p))
    unfold positiveSource
    ring
  exact he ▸ hder

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Comparison of two actual periodic approximations along each characteristic -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness TransportPrimitive

theorem BoundedCutoffSolution.positive_comparison
    {N M H K : ℝ} {f₀ g₀ : Density}
    (S : BoundedCutoffSolution N H f₀) (P : BoundedCutoffSolution M K g₀)
    (hN : 0 < N) (hM : 0 < M) {t : ℝ} (ht : t ∈ Icc 0 H) (ht' : t ≤ K) (p : Phase) :
    |positiveDifference (S.density (t,TorusFlight.flight t p))
      (P.density (t,TorusFlight.flight t p))| ≤ |positiveDifference (f₀ p) (g₀ p)|+
      ∫ r in 0..t,
        |S.characteristicGain (r,p)-P.characteristicGain (r,p)|/
          (1+S.density (r,TorusFlight.flight r p)+P.density (r,TorusFlight.flight r p))+
        S.characteristicLossDefect (r,p)/(1+S.density (r,TorusFlight.flight r p))+
        P.characteristicLossDefect (r,p)/(1+P.density (r,TorusFlight.flight r p))+
        |physicalCharacteristicFrequency S.kineticProfile (r,p)-
          physicalCharacteristicFrequency P.kineticProfile (r,p)| := by
  have hs r (hr : r ∈ Icc 0 t) : S.dampedPath p r = S.density (r,TorusFlight.flight r p) :=
    S.dampedPath_eq ⟨hr.1,hr.2.trans ht.2⟩ p
  have hp r (hr : r ∈ Icc 0 t) : P.dampedPath p r = P.density (r,TorusFlight.flight r p) :=
    P.dampedPath_eq ⟨hr.1,hr.2.trans ht'⟩ p
  have hsu r (hr : r ∈ Icc 0 t) : 0 ≤ S.dampedPath p r := by rw [hs r hr]; exact S.nonnegative _
  have hpu r (hr : r ∈ Icc 0 t) : 0 ≤ P.dampedPath p r := by rw [hp r hr]; exact P.nonnegative _
  have hsa r (_hr : r ∈ Icc 0 t) : 0 ≤ S.characteristicGain (r,p) :=
    (gain_bounds hN S.kineticProfile_measurable (fun q => S.nonnegative _)
      ((r,(TorusFlight.flight r p).1),p.2)).1
  have hpa r (_hr : r ∈ Icc 0 t) : 0 ≤ P.characteristicGain (r,p) :=
    (gain_bounds hM P.kineticProfile_measurable (fun q => P.nonnegative _)
      ((r,(TorusFlight.flight r p).1),p.2)).1
  have hh := positiveDifference_error_bound ht.1
    (S.dampedPath_absolutelyContinuous hN p t) (P.dampedPath_absolutelyContinuous hM p t)
    hsu hpu hsa hpa
    (fun r _ => physicalCharacteristicFrequency_nonneg (f := S.kineticProfile)
      (fun q => S.nonnegative _) (r,p))
    (fun r _ => physicalCharacteristicFrequency_nonneg (f := P.kineticProfile)
      (fun q => P.nonnegative _) (r,p))
    (fun r _ => S.characteristicLossDefect_nonneg hN (r,p))
    (fun r _ => P.characteristicLossDefect_nonneg hM (r,p))
    (S.gain_path_integrable hN p t) (P.gain_path_integrable hM p t)
    (S.frequency_path_integrable hN.le p t) (P.frequency_path_integrable hM.le p t)
    (S.lossDefect_path_integrable hN p t) (P.lossDefect_path_integrable hM p t)
    (S.dampedPath_physical_derivative hN ht p)
    (P.dampedPath_physical_derivative hM ⟨ht.1,ht'⟩ p)
  rw [hs t ⟨ht.1,le_rfl⟩,hp t ⟨ht.1,le_rfl⟩,
    S.dampedPath_initial,P.dampedPath_initial] at hh
  convert hh using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc 0 t := by simpa only [uIcc_of_le ht.1] using hr
  dsimp only
  rw [hs r hr',hp r hr']

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual initial contribution converges with its physical survival factor -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness

def survivingInitial (T : ℝ) (f : Density) (u : (ℝ × Position) × Velocity → ℝ)
    (z : ℝ × Phase) : ℝ := physicalCharacteristicSurvival T u z*f z.2

theorem GlobalCollisionLimit.surviving_initial_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm
      (survivingInitial T (initialApproximation ((G.weakLimit.indices n:ℝ)+1) f)
          (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile-
        survivingInitial T f G.weakLimit.kineticProfile)
      1 ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) atTop (𝓝 0) := by
  let ν : Measure Phase := (volume : Measure Position).prod
    ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))
  have hν : ν ≤ (volume : Measure Phase) := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod_mono le_rfl Measure.restrict_le_self
  have hfi : Integrable f := integrable_of_entropyGauge hfm hf hi
  have hsurv (u : (ℝ × Position) × Velocity → ℝ) (hun : ∀ p, 0 ≤ u p) z :
      |physicalCharacteristicSurvival T u z| ≤ 1 := by
    have h := Published.timeSurvival_bounds
      (μ := volume.restrict (Icc 0 T)) (f := physicalCharacteristicFrequency u)
      (physicalCharacteristicFrequency_nonneg hun) z
    exact (abs_of_pos h.1).trans_le h.2
  exact strong_bounded_product
    (fun n => (initialApproximation_measurable ((G.weakLimit.indices n:ℝ)+1) hfm).comp measurable_snd)
    (hfm.comp measurable_snd) ((hfi.mono_measure hν).comp_snd (volume.restrict (Icc 0 T)))
    (fun n => Published.timeSurvival_measurable (physicalCharacteristicFrequency_measurable
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable))
    (Published.timeSurvival_measurable (physicalCharacteristicFrequency_measurable
      G.weakLimit.kineticProfile_measurable)) 1
    (fun n => hsurv _ (fun _ => (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _))
    (hsurv _ (fun _ => G.weakLimit.nonnegative _))
    (initialApproximation_time_local_strong hfm hf hfi G.weakLimit.increasing T R)
    (G.characteristic_survival_strong hf hi hT hR)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Product-tested physical pairs converge strongly on the same global subsequence -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem GlobalCollisionLimit.pair_product_average_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) {a b : Velocity → ℝ} (ha : Measurable a) (hb : Measurable b)
    (C D : ℝ≥0) (hC : ∀ v, |a v| ≤ C) (hD : ∀ v, |b v| ≤ D) :
    Tendsto (fun n => eLpNorm (fun x : ℝ × Position =>
      (∫ y : Velocity × Velocity, (a y.1*b y.2)*normalizedPair volume
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (x,y))-
      (∫ y : Velocity × Velocity, (a y.1*b y.2)*normalizedPair volume G.weakLimit.kineticProfile (x,y)))
      1 ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))) atTop (𝓝 0) := by
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
  have hFi : ∀ n, Integrable (F n) (μ.prod (volume : Measure Velocity)) :=
    fun n => integrable_of_entropyGauge (hFm n) (hFn n) (hEi n)
  have hmass : UniformIntegrable (fun n => fiberMass volume (F n)) 1 μ :=
    mass_marginal_uniformIntegrable hFm hFn hEi hEb
  have hmassconv := G.mass_strong T hT
  have hAc := G.velocity_average_strong hf hi hT ha C hC
  have hBc := G.velocity_average_strong hf hi hT hb D hD
  apply normalizedPair_product_strong (μ := μ) (ν := (volume : Measure Velocity))
    (f := F) (g := G.weakLimit.kineticProfile) (k := fun p => a p.2) (l := fun p => b p.2)
    hFm hFn (fun p => G.weakLimit.nonnegative _) hFi hmass hmassconv
    (ha.comp measurable_snd) (hb.comp measurable_snd) C.coe_nonneg D.coe_nonneg
    (fun p => hC p.2) (fun p => hD p.2) hAc hBc

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Every continuous compact velocity-pair average converges strongly -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem GlobalCollisionLimit.pair_compact_average_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (k : C(Velocity × Velocity,ℝ)) (hk : HasCompactSupport k) :
    Tendsto (fun n => eLpNorm (fun x : ℝ × Position =>
      pairTestAverage k (normalizedPair volume
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile) x-
      pairTestAverage k (normalizedPair volume G.weakLimit.kineticProfile) x)
      1 ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let F n := (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile
  let q := G.weakLimit.kineticProfile
  have hFm n : Measurable (F n) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
  have hFn n z : 0 ≤ F n z := (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _
  have hUI : UniformIntegrable F 1 (μ.prod volume) :=
    uniformIntegrable_comp (approximatingSolution_compactness_hypotheses f hfm hf hi
      (volume.restrict (Icc 0 T))).1 G.weakLimit.indices
  have hFi n : Integrable (F n) (μ.prod volume) := memLp_one_iff_integrable.mp (hUI.memLp n)
  have hqi : Integrable q (μ.prod volume) := (G.weakLimit.kinetic_weak_on_window hT).2.1
  have hqn z : 0 ≤ q z := G.weakLimit.nonnegative _
  have hqm : Measurable q := G.weakLimit.kineticProfile_measurable
  have hPm n : Measurable (normalizedPair volume (F n)) :=
    normalizedTensor_measurable (fiberMass_measurable (hFm n)) (hFm n) (hFm n)
  have hQm : Measurable (normalizedPair volume q) :=
    normalizedTensor_measurable (fiberMass_measurable hqm) hqm hqm
  have hPi n : Integrable (normalizedPair volume (F n)) (μ.prod (volume : Measure (Velocity × Velocity))) := by
    simpa only [Measure.volume_eq_prod] using normalizedPair_integrable (hFm n) (hFn n) (hFi n)
  have hQi : Integrable (normalizedPair volume q) (μ.prod (volume : Measure (Velocity × Velocity))) := by
    simpa only [Measure.volume_eq_prod] using normalizedPair_integrable hqm hqn hqi
  obtain ⟨D,hD⟩ := hUI.2
  let B : ℝ≥0∞ := max D (eLpNorm (normalizedPair volume q) 1 (μ.prod volume))
  have hB : B ≠ ∞ := ne_of_lt (max_lt (ENNReal.coe_lt_top)
    (memLp_one_iff_integrable.mpr hQi).eLpNorm_lt_top)
  apply strong_compact_pair_tests hPm hQm hPi hQi hB
  · intro n
    have hh := normalizedTensor_L1_le (fiberMass_measurable (hFm n))
      (fun x => integral_nonneg (fun v => hFn n (x,v))) (hFm n) (hFm n)
      (hFn n) (hFn n) (hFi n) (hFi n) (ae_of_all _ (fun _ => le_rfl))
    change eLpNorm (normalizedPair volume (F n)) 1 (μ.prod (volume.prod volume)) ≤
      eLpNorm (F n) 1 (μ.prod volume) at hh
    have hhb : eLpNorm (normalizedPair volume (F n)) 1 (μ.prod volume) ≤ D := by
      simpa only [Measure.volume_eq_prod] using hh.trans (hD n)
    exact hhb.trans (le_max_left _ _)
  · exact le_max_right _ _
  · intro a b ha hb
    obtain ⟨C,hC⟩ := a.continuous.bounded_above_of_compact_support ha
    obtain ⟨D,hD⟩ := b.continuous.bounded_above_of_compact_support hb
    have hC0 : 0 ≤ C := (abs_nonneg (a 0)).trans (hC 0)
    have hD0 : 0 ≤ D := (abs_nonneg (b 0)).trans (hD 0)
    exact G.pair_product_average_strong hf hi hT a.continuous.measurable b.continuous.measurable
      ⟨C,hC0⟩ ⟨D,hD0⟩ hC hD
  · exact hk

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Parameterized compact pair kernels converge strongly with finite parameter measure -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem GlobalCollisionLimit.pair_compact_kernel_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) {Z : Type*} [MeasurableSpace Z]
    (τ : Measure Z) [IsFiniteMeasure τ] {k : Z × (Velocity × Velocity) → ℝ}
    (hk : Measurable k) (C : ℝ) (hC : ∀ p, |k p| ≤ C)
    (hs : ∀ z, Continuous (fun y => k (z,y)) ∧ HasCompactSupport (fun y => k (z,y))) :
    Tendsto (fun n => eLpNorm (fun p : (ℝ × Position) × Z =>
      (∫ y : Velocity × Velocity, k (p.2,y)*normalizedPair volume
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (p.1,y))-
      (∫ y : Velocity × Velocity, k (p.2,y)*normalizedPair volume G.weakLimit.kineticProfile (p.1,y)))
      1 (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod τ)) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let P n := normalizedPair volume (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile
  let Q := normalizedPair volume G.weakLimit.kineticProfile
  have hPm n : Measurable (P n) := normalizedTensor_measurable
    (fiberMass_measurable (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable)
    (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
    (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
  have hUI : UniformIntegrable P 1 (μ.prod (volume : Measure (Velocity × Velocity))) := by
    simpa only [Measure.volume_eq_prod] using uniformIntegrable_comp
      (approximatingSolution_normalizedPair_compactness f hfm hf hi (volume.restrict (Icc 0 T))).1
      G.weakLimit.indices
  have hw := G.normalized_pairs T hT
  obtain ⟨B,hB⟩ := hUI.2
  apply strong_bounded_kernel_averages hPm hw.1
    (fun n => memLp_one_iff_integrable.mp (hUI.memLp n)) hw.2.1
    ENNReal.coe_ne_top hB hk hC
  intro z
  exact G.pair_compact_average_strong hf hi hT ⟨_,(hs z).1⟩ (hs z).2

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Scalar physical velocity averages retain their linear growth -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_velocity_average_strong
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) {T : ℝ} (hT : 0 ≤ T)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) (D : ℝ≥0) (hD : ∀ v, |ψ v| ≤ D*(1+‖v‖)) :
    Tendsto (fun n => eLpNorm (fun z : ℝ × Position =>
      (∫ v, ψ v*(approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (z,v))-
      (∫ v, ψ v*G.weakLimit.kineticProfile (z,v))) 1
        ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let τ : Measure Unit := Measure.dirac ()
  let A n z := ∫ v, ψ v*(approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (z,v)
  let B z := ∫ v, ψ v*G.weakLimit.kineticProfile (z,v)
  have hAm n : Measurable (A n) :=
    ((hψ.comp measurable_snd).mul
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable).stronglyMeasurable.integral_prod_right'.measurable
  have hBm : Measurable B := ((hψ.comp measurable_snd).mul
    G.weakLimit.kineticProfile_measurable).stronglyMeasurable.integral_prod_right'.measurable
  have ht := G.linear_kernel_strong hf hi hT τ
    (k := fun p : Unit × Velocity => ψ p.2) (hψ.comp measurable_snd) D (fun p => hD p.2)
  have he n : eLpNorm ((A n-B) ∘ Prod.fst) 1 (μ.prod τ) = eLpNorm (A n-B) 1 μ :=
    eLpNorm_comp_measurePreserving ((hAm n).sub hBm).aestronglyMeasurable measurePreserving_fst
  change Tendsto (fun n => eLpNorm ((A n-B) ∘ Prod.fst) 1 (μ.prod τ)) atTop (𝓝 0) at ht
  have he' n : (A n-B) = (fun z => A n z-B z) := by ext z; rfl
  change Tendsto (fun n => eLpNorm (fun z => A n z-B z) 1 μ) atTop (𝓝 0)
  simp only [he] at ht
  simpa only [he'] using ht

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Conserved linear moments of the same global collision limit -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.conserved_linear_moment_ae
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) (D : ℝ≥0)
    (hD : ∀ v, |ψ v| ≤ D*(1+‖v‖))
    (hc : ∀ n t, (∫ p : Phase, ψ p.2*(approximatingSolution f hfm n).density (t,p)) =
      ∫ p : Phase, ψ p.2*initialApproximation ((n:ℝ)+1) f p)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      (∫ p : Phase, ψ p.2*G.weakLimit.density (t,p)) = ∫ p : Phase, ψ p.2*f p := by
  let μ := volume.restrict (Icc 0 T)
  let S n := approximatingSolution f hfm (G.weakLimit.indices n)
  let A n (z : ℝ × Position) := ∫ v, ψ v*(S n).kineticProfile (z,v)
  let B (z : ℝ × Position) := ∫ v, ψ v*G.weakLimit.kineticProfile (z,v)
  have hEi n : Integrable (entropyGauge (S n).kineticProfile) ((μ.prod volume).prod volume) :=
    (S n).kinetic_entropy_integrable (μ := μ) (by positivity)
      (approximatingSolution_entropy f hfm hf hi _)
  have hAi n : Integrable (A n) (μ.prod volume) :=
    (linearVelocityTest_integrable (S n).kineticProfile_measurable
      (fun p => (S n).nonnegative _) (hEi n) hψ D hD).integral_prod_left
  have hBi : Integrable B (μ.prod volume) :=
    (linearVelocityTest_integrable G.weakLimit.kineticProfile_measurable
      (fun p => G.weakLimit.nonnegative _) (G.weakLimit.kinetic_entropy_on_window hf hi hT)
      hψ D hD).integral_prod_left
  have hBm : Measurable B := ((hψ.comp measurable_snd).mul
    G.weakLimit.kineticProfile_measurable).stronglyMeasurable.integral_prod_right'.measurable
  have ha n t : (∫ x, A n (t,x)) =
      ∫ p : Phase, ψ p.2*initialApproximation (((G.weakLimit.indices n):ℝ)+1) f p := by
    have hsi := linearVelocityTest_integrable
      ((S n).measurable.comp (measurable_const.prodMk measurable_id))
      (fun p => (S n).nonnegative _) ((S n).finiteEntropy (by positivity) t).2.2 hψ D hD
    have he := integral_prod (fun p : Phase => ψ p.2*(S n).density (t,p)) hsi
    exact he.symm.trans (hc _ t)
  have hout := Published.conserved_marginal_of_strong hAi hBm hBi
    (G.linear_velocity_average_strong hf hi hT hψ D hD)
    ((initialApproximation_linear_moment_tendsto hfm hf hi hψ D hD).comp
      G.weakLimit.increasing.tendsto_atTop)
    (fun n => ae_of_all μ (ha n))
  filter_upwards [hout, (G.weakLimit.finiteEntropy_ae_volume hf hi).filter_mono
    (ae_mono Measure.restrict_le_self)] with t ht hfinite
  have hti := linearVelocityTest_integrable
    (G.weakLimit.measurable.comp (measurable_const.prodMk measurable_id))
    (fun p => G.weakLimit.nonnegative _) hfinite.1.2.2 hψ D hD
  exact (integral_prod (fun p : Phase => ψ p.2*G.weakLimit.density (t,p)) hti).trans ht

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Mass and total momentum of the actual global limit -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.conserved_linear_moment_ae_nonneg
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) (D : ℝ≥0)
    (hD : ∀ v, |ψ v| ≤ D*(1+‖v‖))
    (hc : ∀ n t, (∫ p : Phase, ψ p.2*(approximatingSolution f hfm n).density (t,p)) =
      ∫ p : Phase, ψ p.2*initialApproximation ((n:ℝ)+1) f p) :
    ∀ᵐ t ∂volume, 0 ≤ t →
      (∫ p : Phase, ψ p.2*G.weakLimit.density (t,p)) = ∫ p : Phase, ψ p.2*f p := by
  have hh n := G.conserved_linear_moment_ae hf hi hψ D hD hc (Nat.cast_nonneg n)
  simp only [ae_restrict_iff' measurableSet_Icc] at hh
  filter_upwards [ae_all_iff.mpr hh] with t ht
  intro ht0
  obtain ⟨n,hn⟩ := exists_nat_ge t
  exact ht n ⟨ht0,hn⟩

theorem GlobalCollisionLimit.mass_conservation_ae
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ t ∂volume, 0 ≤ t → (∫ p : Phase, G.weakLimit.density (t,p)) = ∫ p, f p := by
  have hc n t : (∫ p : Phase, (approximatingSolution f hfm n).density (t,p)) =
      ∫ p, initialApproximation ((n:ℝ)+1) f p := by
    let S := approximatingSolution f hfm n
    calc
      _ = ∫ p : Phase, S.density (PositiveIntegral.time ((n:ℝ)+1) t,p) :=
        integral_congr_ae (ae_of_all _ (S.density_clipped (by positivity) t))
      _ = _ := S.mass_conservation (by positivity) (PositiveIntegral.time_bounds (by positivity) t)
  simpa only [one_mul] using G.conserved_linear_moment_ae_nonneg hf hi
    (ψ := fun _ => 1) measurable_const 1 (fun v => by simp only [abs_one,NNReal.coe_one,one_mul]; linarith [norm_nonneg v])
    (fun n t => by simpa only [one_mul] using hc n t)

theorem GlobalCollisionLimit.momentum_conservation_ae
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (i : Fin 3) :
    ∀ᵐ t ∂volume, 0 ≤ t →
      (∫ p : Phase, (p.2 i)*G.weakLimit.density (t,p)) = ∫ p : Phase, (p.2 i)*f p := by
  have hc n t : (∫ p : Phase, (p.2 i)*(approximatingSolution f hfm n).density (t,p)) =
      ∫ p : Phase, (p.2 i)*initialApproximation ((n:ℝ)+1) f p := by
    let S := approximatingSolution f hfm n
    calc
      _ = ∫ p : Phase, (p.2 i)*S.density (PositiveIntegral.time ((n:ℝ)+1) t,p) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun p => congrArg (fun a => (p.2 i)*a) (S.density_clipped (by positivity) t p))
      _ = _ := S.momentum_coordinate_conservation (by positivity) i (PositiveIntegral.time_bounds (by positivity) t)
  apply G.conserved_linear_moment_ae_nonneg hf hi (ψ := fun v => v i) (by fun_prop) 1 _ hc
  intro v
  have hv : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
  simpa only [NNReal.coe_one,one_mul] using hv.trans (by linarith : ‖v‖ ≤ 1+‖v‖)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong local L1 convergence of the actual smoothed outgoing collision averages -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem GlobalCollisionLimit.smoothed_angular_average_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (R : ℝ) (η χ : C(Velocity,ℝ))
    (hη : HasCompactSupport η) (hχ : HasCompactSupport χ) :
    Tendsto (fun n => eLpNorm (fun p : (ℝ × Position) × Velocity =>
      (∫ y : Velocity × Velocity, smoothedAngularKernel η χ (p.2,y)*normalizedPair volume
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (p.1,y))-
      (∫ y : Velocity × Velocity, smoothedAngularKernel η χ (p.2,y)*
        normalizedPair volume G.weakLimit.kineticProfile (p.1,y)))
      1 (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) atTop (𝓝 0) := by
  let : IsFiniteMeasure ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne
  obtain ⟨C,hC⟩ := smoothedAngularKernel_bounded η χ hη hχ
  apply G.pair_compact_kernel_strong hf hi hT
    ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))
    (smoothedAngularKernel_continuous η χ).measurable C hC
  intro z
  exact ⟨(smoothedAngularKernel_continuous η χ).comp (continuous_const.prodMk continuous_id),
    smoothedAngularKernel_support η χ hη z⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Both endpoints of the actual physical survival factors converge -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.two_time_survival_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm
      (Published.twoTimeSurvival (volume.restrict (Icc 0 T))
        (physicalCharacteristicFrequency (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)-
      Published.twoTimeSurvival (volume.restrict (Icc 0 T))
        (physicalCharacteristicFrequency G.weakLimit.kineticProfile))
      1 (((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))).prod
          (volume.restrict (Icc 0 T)))) atTop (𝓝 0) := by
  obtain ⟨hFi,hgi⟩ := G.characteristic_frequency_integrable hf hi hT hR
  exact Published.strong_twoTimeSurvival
    (fun n => physicalCharacteristicFrequency_measurable
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable)
    (physicalCharacteristicFrequency_measurable G.weakLimit.kineticProfile_measurable)
    hFi hgi (G.characteristic_frequency_strong hf hi hT hR)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong convergence of localized physical outgoing angular averages -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem GlobalCollisionLimit.angular_pair_average_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (η φ : C(Velocity,ℝ)) (hη : HasCompactSupport η) :
    Tendsto (fun n => eLpNorm (fun x : ℝ × Position =>
      (∫ y : Velocity × Velocity, (η y.1*η y.2)*
        (∫ ω : Sphere, collisionKernel y.1 y.2 ω*φ (scatterLeft y.1 y.2 ω) ∂sphereArea)*
        normalizedPair volume (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (x,y))-
      (∫ y : Velocity × Velocity, (η y.1*η y.2)*
        (∫ ω : Sphere, collisionKernel y.1 y.2 ω*φ (scatterLeft y.1 y.2 ω) ∂sphereArea)*
        normalizedPair volume G.weakLimit.kineticProfile (x,y)))
      1 ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))) atTop (𝓝 0) :=
  G.pair_compact_average_strong hf hi hT (angularPostCutoffTest η φ)
    (angularPostCutoffTest_hasCompactSupport η φ hη)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
