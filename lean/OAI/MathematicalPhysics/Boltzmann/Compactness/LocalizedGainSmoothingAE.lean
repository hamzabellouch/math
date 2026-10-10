import OAI.MathematicalPhysics.Boltzmann.Branching.SmoothedPrePostIdentity
import OAI.MathematicalPhysics.Boltzmann.Branching.TransportCutoff
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNormalizedGainTranslation
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionDissipation
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionMeasure
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityCutoffEntropyError
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedCollisionRates
import OAI.MathematicalPhysics.Boltzmann.Compactness.PairBoundedTruncation

namespace OAI

section

/-! # Incoming-velocity localization of the actual physical gain -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness
open Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def localizedPostRate (η : C(Velocity,ℝ)) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  (η (scatterLeft z.1.2.1 z.1.2.2 z.2)*η (scatterRight z.1.2.1 z.1.2.2 z.2))*
    massNormalizedPostRate f z

def localizedPhysicalGain (η : C(Velocity,ℝ)) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  ∫ q : Velocity × Sphere, localizedPostRate η f (collisionGrouping.symm (p,q))
    ∂(volume : Measure Velocity).prod sphereArea

theorem localizedPostRate_measurable (η : C(Velocity,ℝ))
    {f : X × Velocity → ℝ} (hfm : Measurable f) : Measurable (localizedPostRate η f) := by
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      η (scatterLeft z.1.2.1 z.1.2.2 z.2)*η (scatterRight z.1.2.1 z.1.2.2 z.2)) := by
    unfold scatterLeft scatterRight normalComponent
    fun_prop
  exact hm.mul (massNormalizedPostRate_measurable hfm)

theorem localizedPostRate_integrable (η : C(Velocity,ℝ)) (hη : HasCompactSupport η)
    {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hi : Integrable (weightedNormalizedPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (localizedPostRate η f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  obtain ⟨B,hB⟩ := η.continuous.bounded_above_of_compact_support hη
  have hB0 : 0 ≤ B := (abs_nonneg (η 0)).trans (hB 0)
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      η (scatterLeft z.1.2.1 z.1.2.2 z.2)*η (scatterRight z.1.2.1 z.1.2.2 z.2)) := by
    unfold scatterLeft scatterRight normalComponent
    fun_prop
  apply (massNormalizedPostRate_integrable hfm hi).bdd_mul hm.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul (hB _) (hB _) (abs_nonneg _) hB0

theorem localizedPhysicalGain_integrable (η : C(Velocity,ℝ)) (hη : HasCompactSupport η)
    {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hi : Integrable (weightedNormalizedPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (localizedPhysicalGain η f) (μ.prod volume) := by
  have h := collision_test_marginal (localizedPostRate η f) (fun _ => (1:ℝ))
    (by simpa only [one_mul] using localizedPostRate_integrable η hη hfm hi)
  change Integrable (fun p => ∫ q : Velocity × Sphere,
    localizedPostRate η f (collisionGrouping.symm (p,q)) ∂(volume : Measure Velocity).prod sphereArea)
      (μ.prod volume)
  simpa only [one_mul] using h.1

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Identifying the localized physical gain with the linear pair operator -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness
variable {X : Type*}

def localizedPair (η : C(Velocity,ℝ)) (f : X × Velocity → ℝ)
    (z : X × (Velocity × Velocity)) : ℝ :=
  (η z.2.1*η z.2.2)*normalizedPair volume f z

theorem localizedPair_preRate (η : C(Velocity,ℝ)) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    pairPreRate (localizedPair η f) z =
      (η z.1.2.1*η z.1.2.2)*massNormalizedPreRate f z := by
  rw [massNormalizedPreRate_eq_pair]
  unfold pairPreRate localizedPair
  ring

theorem localizedPair_postRate (η : C(Velocity,ℝ)) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    pairPostRate (localizedPair η f) z = localizedPostRate η f z := by
  rw [pairPostRate,localizedPair_preRate]
  rfl

theorem localizedPhysicalGain_eq_pairGain [MeasurableSpace X] (η : C(Velocity,ℝ)) (f : X × Velocity → ℝ) :
    localizedPhysicalGain η f = pairGain (localizedPair η f) := by
  funext p
  unfold localizedPhysicalGain pairGain
  apply integral_congr_ae
  exact ae_of_all _ (fun q => (localizedPair_postRate η f _).symm)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # The entropy velocity tail removes incoming localization of the gain -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem exists_velocity_unit_cutoff {R : ℝ} (hR : 0 < R) :
    ∃ η : C(Velocity,ℝ), HasCompactSupport η ∧
      (∀ v, 0 ≤ η v) ∧ (∀ v, η v ≤ 1) ∧ (∀ v, ‖v‖ ≤ R → η v = 1) := by
  let b : ContDiffBump (0 : Velocity) := ⟨R,R+1,hR,by linarith⟩
  let η : C(Velocity,ℝ) := ⟨b,b.continuous⟩
  refine ⟨η,b.hasCompactSupport,fun v => b.nonneg,fun v => b.le_one,?_⟩
  intro v hv
  apply b.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall,dist_zero_right] using hv

omit [MeasurableSpace X] in
theorem localizedPair_weight (η : C(Velocity,ℝ)) (f : X × Velocity → ℝ) :
    momentPair (localizedPair η f) =
      fun z => (η z.2.1*η z.2.2)*weightedNormalizedPair f z := by
  funext z
  unfold momentPair localizedPair weightedNormalizedPair pairVelocityWeight
  ring

theorem localizedGain_tail_le {R C : ℝ} (hR : 0 < R)
    (η : C(Velocity,ℝ)) (hη0 : ∀ v, 0 ≤ η v) (hη1 : ∀ v, η v ≤ 1)
    (hone : ∀ v, ‖v‖ ≤ R → η v = 1)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyGauge f) (μ.prod volume))
    (hb : (∫ p, entropyGauge f p ∂μ.prod volume) ≤ C) :
    eLpNorm (fun p => pairGain (normalizedPair volume f) p-localizedPhysicalGain η f p)
      1 (μ.prod volume) ≤ sphereArea univ*ENNReal.ofReal (8*C/R) := by
  let w : X × (Velocity × Velocity) → ℝ := fun z => η z.2.1*η z.2.2
  have hwm : Measurable w :=
    (η.continuous.measurable.comp measurable_snd.fst).mul
      (η.continuous.measurable.comp measurable_snd.snd)
  have hw0 z : 0 ≤ w z := mul_nonneg (hη0 _) (hη0 _)
  have hw1 z : w z ≤ 1 := by
    dsimp only [w]
    nlinarith [hη0 z.2.1,hη0 z.2.2,hη1 z.2.1,hη1 z.2.2]
  have hpm : Measurable (normalizedPair volume f) :=
    normalizedTensor_measurable (fiberMass_measurable hfm) hfm hfm
  have hqm : Measurable (localizedPair η f) := hwm.mul hpm
  have hwi : Integrable (weightedNormalizedPair f)
      (μ.prod (volume : Measure (Velocity × Velocity))) := by
    simpa only [Measure.volume_eq_prod] using weightedNormalizedPair_integrable hfm hf hi
  have hqi : Integrable (momentPair (localizedPair η f))
      (μ.prod (volume : Measure (Velocity × Velocity))) := by
    rw [localizedPair_weight]
    apply hwi.bdd_mul hwm.aestronglyMeasurable (c := 1)
    exact ae_of_all _ (fun z => by rw [Real.norm_of_nonneg (hw0 z)]; exact hw1 z)
  have hpn z : 0 ≤ weightedNormalizedPair f z := by
    have hd : 0 ≤ 1+fiberMass volume f z.1 := by
      have hm : 0 ≤ fiberMass volume f z.1 := integral_nonneg (fun v => hf (z.1,v))
      linarith
    exact mul_nonneg (by dsimp [pairVelocityWeight]; positivity)
      (div_nonneg (mul_nonneg (hf _) (hf _)) hd)
  have he : eLpNorm (momentPair (fun z => normalizedPair volume f z-localizedPair η f z))
      1 (μ.prod (volume : Measure (Velocity × Velocity))) ≤
      eLpNorm (fun z => weightedNormalizedPair f z-pairVelocityCut R f z)
        1 (μ.prod (volume : Measure (Velocity × Velocity))) := by
    apply eLpNorm_mono_ae (momentPair_measurable (hpm.sub hqm)).aestronglyMeasurable
    filter_upwards [] with z
    change ‖momentPair (fun y => normalizedPair volume f y-localizedPair η f y) z‖ ≤ _
    have heq : momentPair (fun y => normalizedPair volume f y-localizedPair η f y) z =
        (1-w z)*weightedNormalizedPair f z := by
      dsimp only [momentPair,localizedPair,weightedNormalizedPair,pairVelocityWeight,w]
      ring
    rw [heq]
    by_cases hv : ‖z.2.1‖ ≤ R ∧ ‖z.2.2‖ ≤ R
    · have hw : w z = 1 := by simp only [w,hone _ hv.1,hone _ hv.2,one_mul]
      simp only [hw,sub_self,zero_mul,norm_zero]
      exact norm_nonneg _
    · rw [pairVelocityCut,ite_eq_right hv,sub_zero,
        Real.norm_of_nonneg (mul_nonneg (sub_nonneg.mpr (hw1 z)) (hpn z)),
        Real.norm_of_nonneg (hpn z)]
      nlinarith [mul_nonneg (hw0 z) (hpn z)]
  rw [localizedPhysicalGain_eq_pairGain]
  exact (pairGain_moment_difference_le hpm hqm hwi hqi).trans
    (mul_le_mul' le_rfl (he.trans (pairVelocityCut_L1_error hR hfm hf hi hb)))

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Causal localized transport sources and their velocity support -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.TransportCutoff

def localizedSource (U : ℝ) (χ f Q : KineticPhase → ℝ) (z : KineticPhase) : ℝ :=
  if z.1.1 ∈ Icc 0 U then χ z*Q z+(transportDerivative χ z+χ z)*f z else 0

theorem localizedSource_causal (U : ℝ) (χ f Q : KineticPhase → ℝ)
    (z : KineticPhase) (ht : z.1.1 < 0) : localizedSource U χ f Q z = 0 := by
  apply ite_eq_right
  exact fun h => not_le_of_gt ht h.1

theorem localizedSource_on {U : ℝ} (χ f Q : KineticPhase → ℝ)
    (z : KineticPhase) (ht : z.1.1 ∈ Icc 0 U) :
    localizedSource U χ f Q z = χ z*Q z+(transportDerivative χ z+χ z)*f z := ite_eq_left ht

theorem localizedSource_velocity_support {U R : ℝ} {χ : KineticPhase → ℝ}
    (hχ : tsupport χ ⊆ {z | ‖z.2‖ ≤ R}) (f Q : KineticPhase → ℝ)
    (z : KineticPhase) (hv : R < ‖z.2‖) : localizedSource U χ f Q z = 0 := by
  have hz : z ∉ tsupport χ := fun h => not_le_of_gt hv (hχ h)
  have hc : χ z = 0 := image_eq_zero_of_notMem_tsupport hz
  have hd := transportDerivative_eq_zero hz
  unfold localizedSource
  split_ifs <;> simp only [hc,hd,zero_mul,add_zero]

theorem localizedSource_measurable {U : ℝ} {χ f Q : KineticPhase → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hf : Measurable f) (hQ : Measurable Q) :
    Measurable (localizedSource U χ f Q) := by
  apply Measurable.ite
  · exact measurableSet_Icc.preimage measurable_fst.fst
  · exact (hχ.continuous.measurable.mul hQ).add
      (((transportDerivative_continuous hχ).measurable.add hχ.continuous.measurable).mul hf)
  · exact measurable_const

end BoltzmannNonuniqueness.TransportCutoff

end

end

section

/-! # Velocity translations of the actual localized physical gains -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem localizedGain_translation
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (η : C(Velocity,ℝ)) (hη : HasCompactSupport η)
    {a : ℕ → Velocity} (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ p,
      |localizedPhysicalGain η (f n) (p.1,p.2+a n)-localizedPhysicalGain η (f n) p|
      ∂μ.prod volume) atTop (𝓝 0) := by
  obtain ⟨B,hB⟩ := η.continuous.bounded_above_of_compact_support hη
  have hB0 : 0 ≤ B := (abs_nonneg (η 0)).trans (hB 0)
  let K : ℝ≥0 := ⟨B^2,sq_nonneg B⟩
  have hw : Measurable (fun z : X × (Velocity × Velocity) => η z.2.1*η z.2.2) := by fun_prop
  have hK (z : X × (Velocity × Velocity)) : |η z.2.1*η z.2.2| ≤ K := by
    change |η z.2.1*η z.2.2| ≤ B^2
    rw [abs_mul,pow_two]
    exact mul_le_mul (hB _) (hB _) (abs_nonneg _) hB0
  have ht := weighted_normalizedGain_translation (μ := μ) hfm hf hi hb hw K hK ha
  simp_rw [localizedPhysicalGain_eq_pairGain]
  change Tendsto (fun n => ∫ p,
    |pairGain (fun z => η z.2.1*η z.2.2*normalizedPair volume (f n) z) (p.1,p.2+a n)-
      pairGain (fun z => η z.2.1*η z.2.2*normalizedPair volume (f n) z) p|
      ∂μ.prod volume) atTop (𝓝 0)
  exact ht

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Velocity smoothing of the genuine localized gain equals its incoming pair formula -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness
open Compactness
variable {X : Type*} [MeasurableSpace X]

theorem localizedPhysicalGain_smoothing (η χ : C(Velocity,ℝ))
    (hη : HasCompactSupport η) (hχ : HasCompactSupport χ)
    (f : X × Velocity → ℝ) (x : X) (v : Velocity)
    (hpre : Integrable (fun z : (Velocity × Velocity) × Sphere =>
      massNormalizedPreRate f ((x,z.1),z.2)) ((volume : Measure (Velocity × Velocity)).prod sphereArea))
    (hpost : Integrable (fun z : (Velocity × Velocity) × Sphere =>
      localizedPostRate η f ((x,z.1),z.2)) ((volume : Measure (Velocity × Velocity)).prod sphereArea)) :
    (∫ u : Velocity, χ (v-u)*localizedPhysicalGain η f (x,u)) =
    ∫ y : Velocity × Velocity, smoothedAngularKernel η χ (v,y)*normalizedPair volume f (x,y) := by
  obtain ⟨B,hB⟩ := η.continuous.bounded_above_of_compact_support hη
  obtain ⟨D,hD⟩ := χ.continuous.bounded_above_of_compact_support hχ
  have hB0 : 0 ≤ B := (abs_nonneg (η 0)).trans (hB 0)
  have hD0 : 0 ≤ D := (abs_nonneg (χ 0)).trans (hD 0)
  have hm : Measurable (fun z : (Velocity × Velocity) × Sphere =>
      (η z.1.1*η z.1.2)*χ (v-scatterLeft z.1.1 z.1.2 z.2)) := by
    unfold scatterLeft normalComponent
    fun_prop
  have hi : Integrable (fun z : (Velocity × Velocity) × Sphere =>
      (η z.1.1*η z.1.2)*χ (v-scatterLeft z.1.1 z.1.2 z.2)*
        massNormalizedPreRate f ((x,z.1),z.2))
      ((volume : Measure (Velocity × Velocity)).prod sphereArea) := by
    apply hpre.bdd_mul hm.aestronglyMeasurable (c := B*B*D)
    filter_upwards [] with z
    simp only [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (mul_le_mul (hB _) (hB _) (abs_nonneg _) hB0) (hD _)
      (abs_nonneg _) (mul_nonneg hB0 hB0)
  have hposteq := collision_fiber_test_fubini hpost
    (χ.continuous.measurable.comp (measurable_const.sub measurable_id)) D (fun u => hD (v-u))
  calc
    _ = ∫ ω : Sphere, (∫ y : Velocity × Velocity,
        (η (scatterLeft y.1 y.2 ω)*η (scatterRight y.1 y.2 ω))*χ (v-y.1)*
          massNormalizedPostRate f ((x,y),ω)) ∂sphereArea := by
      change (∫ u : Velocity, χ (v-u)*localizedPhysicalGain η f (x,u)) = _ at hposteq
      rw [hposteq]
      apply integral_congr_ae
      filter_upwards [] with ω
      apply integral_congr_ae
      filter_upwards [] with y
      dsimp only [localizedPostRate,Function.comp_apply,Pi.sub_apply,Function.const_apply,id_eq]
      ring
    _ = ∫ ω : Sphere, (∫ y : Velocity × Velocity,
        (η y.1*η y.2)*χ (v-scatterLeft y.1 y.2 ω)*massNormalizedPreRate f ((x,y),ω)) ∂sphereArea :=
      (smoothed_pre_post_normals η χ f x v).symm
    _ = ∫ y : Velocity × Velocity, ∫ ω : Sphere,
        (η y.1*η y.2)*χ (v-scatterLeft y.1 y.2 ω)*massNormalizedPreRate f ((x,y),ω) ∂sphereArea :=
      (integral_prod_symm _ hi).symm.trans (integral_prod _ hi)
    _ = _ := smoothed_preRate_pair_identity η χ f x v

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The physical gain convolution identity on a common full-measure base set -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness
open Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

local instance collisionRateFiberSFinite : SFinite ((volume : Measure (Velocity × Velocity)).prod sphereArea) :=
  Measure.prod.instSFinite

theorem collision_rate_fibers {r : (X × (Velocity × Velocity)) × Sphere → ℝ}
    (hi : Integrable r ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    ∀ᵐ x ∂μ, Integrable (fun z : (Velocity × Velocity) × Sphere => r ((x,z.1),z.2))
      ((volume : Measure (Velocity × Velocity)).prod sphereArea) := by
  have hmp := measurePreserving_prodAssoc μ (volume : Measure (Velocity × Velocity)) sphereArea
  have hh := hmp.symm.integrable_comp_of_integrable hi
  exact hh.prod_right_ae

theorem localizedPhysicalGain_smoothing_ae (η χ : C(Velocity,ℝ))
    (hη : HasCompactSupport η) (hχ : HasCompactSupport χ)
    {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hi : Integrable (weightedNormalizedPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    ∀ᵐ x ∂μ, ∀ v : Velocity,
      (∫ u : Velocity, χ (v-u)*localizedPhysicalGain η f (x,u)) =
      ∫ y : Velocity × Velocity, smoothedAngularKernel η χ (v,y)*normalizedPair volume f (x,y) := by
  filter_upwards [collision_rate_fibers (massNormalizedPreRate_integrable hfm hi),
    collision_rate_fibers (localizedPostRate_integrable η hη hfm hi)] with x hx hy
  intro v
  exact localizedPhysicalGain_smoothing η χ hη hχ f x v hx hy

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
