import OAI.MathematicalPhysics.Boltzmann.Branching.GainNonnegative
import OAI.MathematicalPhysics.Boltzmann.Collision.AngularPairTests
import OAI.MathematicalPhysics.Boltzmann.Model

namespace OAI

section

/-!
# Measure preservation for a hard-sphere collision

For each fixed unit normal, the pre/post-collisional map is an orthogonal
involution on the six-dimensional velocity-pair space. Its Euclidean norm is
implemented with `WithLp 2`; the final measure statement uses the ordinary
product of the two three-dimensional Lebesgue measures.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

/-- The pre/post-collisional map, with the collision normal fixed. -/
def scatterPair (ω : Velocity) (p : Velocity × Velocity) : Velocity × Velocity :=
  (scatterLeft p.1 p.2 ω, scatterRight p.1 p.2 ω)

theorem scatterPair_involutive (ω : Velocity) (hω : ‖ω‖ = 1) :
    Function.Involutive (scatterPair ω) := by
  intro p
  exact Prod.ext (scatterLeft_involutive p.1 p.2 ω hω)
    (scatterRight_involutive p.1 p.2 ω hω)

/-- Linearity holds even before imposing the unit-normal condition. -/
def scatterLinearMap (ω : Velocity) :
    (Velocity × Velocity) →ₗ[ℝ] (Velocity × Velocity) where
  toFun := scatterPair ω
  map_add' p q := by
    apply Prod.ext
    · simp only [scatterPair, scatterLeft, normalComponent, Prod.fst_add, Prod.snd_add,
        inner_sub_left, inner_add_left]
      module
    · simp only [scatterPair, scatterRight, normalComponent, Prod.fst_add, Prod.snd_add,
        inner_sub_left, inner_add_left]
      module
  map_smul' c p := by
    apply Prod.ext
    · simp only [scatterPair, scatterLeft, normalComponent, Prod.smul_fst, Prod.smul_snd,
        inner_sub_left, real_inner_smul_left, RingHom.id_apply]
      module
    · simp only [scatterPair, scatterRight, normalComponent, Prod.smul_fst, Prod.smul_snd,
        inner_sub_left, real_inner_smul_left, RingHom.id_apply]
      module

/-- A unit-normal collision is a linear involution. -/
def scatterLinearEquiv (ω : Velocity) (hω : ‖ω‖ = 1) :
    (Velocity × Velocity) ≃ₗ[ℝ] (Velocity × Velocity) :=
  LinearEquiv.ofInvolutive (scatterLinearMap ω) (scatterPair_involutive ω hω)

/-- The Euclidean velocity-pair space, whose norm squared is total kinetic energy. -/
abbrev EuclideanVelocityPair := WithLp 2 (Velocity × Velocity)

/-- The collision linear equivalence transported to the Euclidean pair norm. -/
def scatterEuclideanLinearEquiv (ω : Velocity) (hω : ‖ω‖ = 1) :
    EuclideanVelocityPair ≃ₗ[ℝ] EuclideanVelocityPair :=
  ((WithLp.linearEquiv 2 ℝ (Velocity × Velocity)).trans (scatterLinearEquiv ω hω)).trans
    (WithLp.linearEquiv 2 ℝ (Velocity × Velocity)).symm

theorem scatterEuclideanLinearEquiv_apply (ω : Velocity) (hω : ‖ω‖ = 1)
    (p : EuclideanVelocityPair) :
    scatterEuclideanLinearEquiv ω hω p = WithLp.toLp 2 (scatterPair ω (WithLp.ofLp p)) :=
  rfl

/-- Conservation of total kinetic energy makes the collision map an isometry. -/
def scatterLinearIsometryEquiv (ω : Velocity) (hω : ‖ω‖ = 1) :
    EuclideanVelocityPair ≃ₗᵢ[ℝ] EuclideanVelocityPair where
  toLinearEquiv := scatterEuclideanLinearEquiv ω hω
  norm_map' p := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    exact scatter_energy p.fst p.snd ω hω

/-- Fixed-normal pre/post collision change of variables preserves product Lebesgue measure. -/
theorem scatterPair_measurePreserving (ω : Velocity) (hω : ‖ω‖ = 1) :
    MeasurePreserving (scatterPair ω)
      ((volume : Measure Velocity).prod volume)
      ((volume : Measure Velocity).prod volume) := by
  have h := (WithLp.volume_preserving_ofLp Velocity Velocity).comp
    ((scatterLinearIsometryEquiv ω hω).measurePreserving.comp
      (WithLp.volume_preserving_toLp Velocity Velocity))
  exact h

theorem scatterPair_measurableEmbedding (ω : Velocity) (hω : ‖ω‖ = 1) :
    MeasurableEmbedding (scatterPair ω) :=
  (scatterLinearEquiv ω hω).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding

/-- The unweighted pre/post-collisional change-of-variables identity. -/
theorem integral_scatterPair (ω : Velocity) (hω : ‖ω‖ = 1)
    (F : Velocity × Velocity → ℝ) :
    (∫ p, F (scatterPair ω p) ∂((volume : Measure Velocity).prod volume)) =
      ∫ p, F p ∂((volume : Measure Velocity).prod volume) :=
  (scatterPair_measurePreserving ω hω).integral_comp
    (scatterPair_measurableEmbedding ω hω) F

/-- The hard-sphere angular factor is unchanged by the pre/post change of variables. -/
theorem integral_collisionKernel_scatterPair (ω : Velocity) (hω : ‖ω‖ = 1)
    (F : Velocity × Velocity → ℝ) :
    (∫ p, collisionKernel p.1 p.2 ω * F (scatterPair ω p)
      ∂((volume : Measure Velocity).prod volume)) =
      ∫ p, collisionKernel p.1 p.2 ω * F p
        ∂((volume : Measure Velocity).prod volume) := by
  simpa only [scatterPair, collisionKernel_scatter _ _ ω hω] using
    integral_scatterPair ω hω (fun p => collisionKernel p.1 p.2 ω * F p)

/-- The relative velocity is reflected in the plane normal to the collision normal. -/
theorem scatter_relative_velocity (v w ω : Velocity) :
    scatterLeft v w ω - scatterRight v w ω =
      (v - w) - (2 * normalComponent v w ω) • ω := by
  unfold scatterLeft scatterRight
  module

/-- A unit-normal collision preserves the relative speed. -/
theorem scatter_relative_speed (v w ω : Velocity) (hω : ‖ω‖ = 1) :
    ‖scatterLeft v w ω - scatterRight v w ω‖ = ‖v - w‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [scatter_relative_velocity, norm_sub_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, hω, mul_one, sq_abs]
  unfold normalComponent
  ring

/-- The common relative-speed cutoff used for both pre- and post-collisional variables. -/
def collisionCutoff (b : ℝ) : Set (Velocity × Velocity) := {p | ‖p.1 - p.2‖ < b}

theorem collisionCutoff_preimage_scatterPair (b : ℝ) (ω : Velocity) (hω : ‖ω‖ = 1) :
    scatterPair ω ⁻¹' collisionCutoff b = collisionCutoff b := by
  ext p
  simp only [Set.mem_preimage, collisionCutoff, Set.mem_ofPred_eq, scatterPair,
    scatter_relative_speed _ _ ω hω]

/-- The cutoff indicator commutes with pre/post-collisional substitution. -/
theorem collisionCutoff_indicator_scatterPair (b : ℝ) (ω : Velocity) (hω : ‖ω‖ = 1)
    (F : Velocity × Velocity → ℝ) (p : Velocity × Velocity) :
    (collisionCutoff b).indicator F (scatterPair ω p) =
      (collisionCutoff b).indicator (fun q => F (scatterPair ω q)) p := by
  simp only [Set.indicator, collisionCutoff, Set.mem_ofPred_eq, scatterPair,
    scatter_relative_speed _ _ ω hω]
  rfl

/-- The collision map preserves Lebesgue measure restricted to the common cutoff. -/
theorem scatterPair_cutoff_measurePreserving (b : ℝ) (ω : Velocity) (hω : ‖ω‖ = 1) :
    MeasurePreserving (scatterPair ω)
      (((volume : Measure Velocity).prod volume).restrict (collisionCutoff b))
      (((volume : Measure Velocity).prod volume).restrict (collisionCutoff b)) := by
  simpa only [collisionCutoff_preimage_scatterPair b ω hω] using
    (scatterPair_measurePreserving ω hω).restrict_preimage_emb
      (scatterPair_measurableEmbedding ω hω) (collisionCutoff b)

/-- Unweighted substitution on the exact strict relative-speed cutoff. -/
theorem integral_cutoff_scatterPair (b : ℝ) (ω : Velocity) (hω : ‖ω‖ = 1)
    (F : Velocity × Velocity → ℝ) :
    (∫ p in collisionCutoff b, F (scatterPair ω p)
      ∂((volume : Measure Velocity).prod volume)) =
      ∫ p in collisionCutoff b, F p ∂((volume : Measure Velocity).prod volume) :=
  (scatterPair_cutoff_measurePreserving b ω hω).integral_comp
    (scatterPair_measurableEmbedding ω hω) F

/-- Kernel-weighted substitution on the manuscript's common collision cutoff. -/
theorem integral_cutoff_collisionKernel_scatterPair (b : ℝ) (ω : Velocity) (hω : ‖ω‖ = 1)
    (F : Velocity × Velocity → ℝ) :
    (∫ p in collisionCutoff b, collisionKernel p.1 p.2 ω * F (scatterPair ω p)
      ∂((volume : Measure Velocity).prod volume)) =
      ∫ p in collisionCutoff b, collisionKernel p.1 p.2 ω * F p
        ∂((volume : Measure Velocity).prod volume) := by
  simpa only [scatterPair, collisionKernel_scatter _ _ ω hω] using
    integral_cutoff_scatterPair b ω hω (fun p => collisionKernel p.1 p.2 ω * F p)

theorem normalComponent_neg_normal (v w ω : Velocity) :
    normalComponent v w (-ω) = -normalComponent v w ω := by
  simp only [normalComponent, inner_neg_right]

/-- Opposite normal representatives describe exactly the same scattering. -/
theorem scatterLeft_neg_normal (v w ω : Velocity) :
    scatterLeft v w (-ω) = scatterLeft v w ω := by
  simp only [scatterLeft, normalComponent_neg_normal, neg_smul_neg]

theorem scatterRight_neg_normal (v w ω : Velocity) :
    scatterRight v w (-ω) = scatterRight v w ω := by
  simp only [scatterRight, normalComponent_neg_normal, neg_smul_neg]

theorem collisionKernel_neg_normal (v w ω : Velocity) :
    collisionKernel v w (-ω) = collisionKernel v w ω := by
  simp only [collisionKernel, normalComponent_neg_normal, abs_neg]

theorem scatterPair_neg_normal (ω : Velocity) (p : Velocity × Velocity) :
    scatterPair (-ω) p = scatterPair ω p := by
  simp only [scatterPair, scatterLeft_neg_normal, scatterRight_neg_normal]

end BoltzmannNonuniqueness

end

end

section

/-! # The relative-speed cutoff used in the finite approximations -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCutoff

def rate (b : ℝ) (v w : Velocity) : ℝ := if ‖v - w‖ < b then ‖v - w‖ else 0

def kernel (b : ℝ) (v w : Velocity) (ω : Sphere) : ℝ :=
  if ‖v - w‖ < b then collisionKernel v w ω else 0

def frequency (b : ℝ) (f : Velocity → ℝ) (v : Velocity) : ℝ :=
  2 * Real.pi * ∫ w, rate b v w * f w

def integrand (b : ℝ) (f : Velocity → ℝ) (v : Velocity) (p : Velocity × Sphere) : ℝ :=
  kernel b v p.1 p.2 * f (scatterLeft v p.1 p.2) * f (scatterRight v p.1 p.2)

def gain (b : ℝ) (f : Velocity → ℝ) (v : Velocity) : ℝ :=
  ∫ p, integrand b f v p ∂((volume : Measure Velocity).prod sphereArea)

theorem kernel_scatter (b : ℝ) (v w : Velocity) (ω : Sphere) :
    kernel b (scatterLeft v w ω) (scatterRight v w ω) ω = kernel b v w ω := by
  simp only [kernel, scatter_relative_speed v w ω (mem_sphere_zero_iff_norm.mp ω.property),
    collisionKernel_scatter v w ω (mem_sphere_zero_iff_norm.mp ω.property)]

theorem rate_nonneg (b : ℝ) (v w : Velocity) : 0 ≤ rate b v w := by
  unfold rate
  split_ifs <;> positivity

theorem rate_le {b : ℝ} (hb : 0 ≤ b) (v w : Velocity) : rate b v w ≤ b := by
  unfold rate
  split_ifs with h
  · exact h.le
  · exact hb

theorem measurable_rate (b : ℝ) (v : Velocity) : Measurable (rate b v) := by
  unfold rate
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop) measurable_const

theorem integrable_frequency {b : ℝ} (hb : 0 ≤ b) {f : Velocity → ℝ} (hf : Integrable f)
    (v : Velocity) : Integrable (fun w => rate b v w * f w) := by
  apply (hf.norm.const_mul b).mono' ((measurable_rate b v).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with w
  dsimp only [Pi.mul_apply]
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (rate_nonneg b v w)]
  exact mul_le_mul_of_nonneg_right (rate_le hb v w) (norm_nonneg _)

theorem abs_frequency_le {b : ℝ} (hb : 0 ≤ b) {f : Velocity → ℝ} (hf : Integrable f)
    (v : Velocity) : |frequency b f v| ≤ 2 * Real.pi * b * ∫ w, |f w| := by
  have hi := integrable_frequency hb hf v
  have hm : Integrable (fun w => b * |f w|) := by simpa only [Real.norm_eq_abs] using hf.norm.const_mul b
  have hpoint (w : Velocity) : |rate b v w * f w| ≤ b * |f w| := by
    rw [abs_mul, abs_of_nonneg (rate_nonneg b v w)]
    exact mul_le_mul_of_nonneg_right (rate_le hb v w) (abs_nonneg _)
  calc
    _ = 2 * Real.pi * |∫ w, rate b v w * f w| := by
      rw [frequency, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    _ ≤ 2 * Real.pi * ∫ w, |rate b v w * f w| :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by positivity)
    _ ≤ 2 * Real.pi * ∫ w, b * |f w| := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono (by simpa only [Real.norm_eq_abs] using hi.norm) hm hpoint
    _ = _ := by rw [integral_const_mul]; ring

theorem kernel_nonneg (b : ℝ) (v w : Velocity) (ω : Sphere) : 0 ≤ kernel b v w ω := by
  unfold kernel
  split_ifs
  · exact collisionKernel_nonneg _ _ _
  · exact le_rfl

theorem kernel_le (b : ℝ) (v w : Velocity) (ω : Sphere) : kernel b v w ω ≤ collisionKernel v w ω := by
  unfold kernel
  split_ifs
  · exact le_rfl
  · exact collisionKernel_nonneg _ _ _

theorem integrand_le (b : ℝ) {f : Velocity → ℝ} (hf : ∀ w, 0 ≤ f w)
    (v : Velocity) (p : Velocity × Sphere) : integrand b f v p ≤ GainOrder.integrand f v p := by
  unfold integrand GainOrder.integrand
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (kernel_le b v p.1 p.2) (hf _)) (hf _)

theorem integrable_gain (b : ℝ) {f : Velocity → ℝ} (hm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    (v : Velocity) (hi : Integrable (GainOrder.integrand f v) ((volume : Measure Velocity).prod sphereArea)) :
    Integrable (integrand b f v) ((volume : Measure Velocity).prod sphereArea) := by
  have he (p : Velocity × Sphere) : integrand b f v p =
      if ‖v - p.1‖ < b then GainOrder.integrand f v p else 0 := by
    unfold integrand kernel GainOrder.integrand
    split_ifs <;> simp only [zero_mul]
  change Integrable (fun p => integrand b f v p) _
  simp_rw [he]
  apply hi.mono'
  · exact ((GainOrder.integrand_measurable hm v).ite
      (measurableSet_lt (by fun_prop) measurable_const) measurable_const).aestronglyMeasurable
  · filter_upwards [] with p
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (GainOrder.integrand_nonneg hf v p)]
    · simpa only [norm_zero] using GainOrder.integrand_nonneg hf v p

theorem gain_le (b : ℝ) {f : Velocity → ℝ} (hm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    (v : Velocity) (x : Position)
    (hi : Integrable (GainOrder.integrand f v) ((volume : Measure Velocity).prod sphereArea)) :
    gain b f v ≤ BoltzmannNonuniqueness.gain (fun p => f p.2) x v :=
  integral_mono (integrable_gain b hm hf v hi) hi (integrand_le b hf v)

end BoltzmannNonuniqueness.CollisionCutoff

end

end

section

/-! # Collision operators respect almost-everywhere representatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.CollisionNullSets

theorem left_pair (ω : Sphere) : QuasiMeasurePreserving
    (fun p : Velocity × Velocity => scatterLeft p.1 p.2 ω)
    ((volume : Measure Velocity).prod volume) volume :=
  MeasureTheory.QuasiMeasurePreserving.fst
    (scatterPair_measurePreserving ω (mem_sphere_zero_iff_norm.mp ω.property)).quasiMeasurePreserving

theorem right_pair (ω : Sphere) : QuasiMeasurePreserving
    (fun p : Velocity × Velocity => scatterRight p.1 p.2 ω)
    ((volume : Measure Velocity).prod volume) volume :=
  MeasureTheory.QuasiMeasurePreserving.snd
    (scatterPair_measurePreserving ω (mem_sphere_zero_iff_norm.mp ω.property)).quasiMeasurePreserving

def left (p : Velocity × (Velocity × Sphere)) : Velocity := scatterLeft p.1 p.2.1 p.2.2
def right (p : Velocity × (Velocity × Sphere)) : Velocity := scatterRight p.1 p.2.1 p.2.2

theorem left_quasiMeasurePreserving : QuasiMeasurePreserving left
    ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)) volume := by
  let : SFinite ((volume : Measure Velocity).prod (volume : Measure Velocity)) := Measure.prod.instSFinite
  have h : QuasiMeasurePreserving
      (fun p : (Velocity × Velocity) × Sphere => scatterLeft p.1.1 p.1.2 p.2)
      (((volume : Measure Velocity).prod volume).prod sphereArea) volume := by
    apply MeasureTheory.QuasiMeasurePreserving.prod_of_left
    · unfold scatterLeft normalComponent
      fun_prop
    · exact ae_of_all _ left_pair
  exact h.comp ((measurePreserving_prodAssoc (volume : Measure Velocity) volume sphereArea).symm
    MeasurableEquiv.prodAssoc).quasiMeasurePreserving

theorem right_quasiMeasurePreserving : QuasiMeasurePreserving right
    ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)) volume := by
  let : SFinite ((volume : Measure Velocity).prod (volume : Measure Velocity)) := Measure.prod.instSFinite
  have h : QuasiMeasurePreserving
      (fun p : (Velocity × Velocity) × Sphere => scatterRight p.1.1 p.1.2 p.2)
      (((volume : Measure Velocity).prod volume).prod sphereArea) volume := by
    apply MeasureTheory.QuasiMeasurePreserving.prod_of_left
    · unfold scatterRight normalComponent
      fun_prop
    · exact ae_of_all _ right_pair
  exact h.comp ((measurePreserving_prodAssoc (volume : Measure Velocity) volume sphereArea).symm
    MeasurableEquiv.prodAssoc).quasiMeasurePreserving

theorem gain_congr {f g : Velocity → ℝ} (hfg : f =ᵐ[volume] g) :
    ∀ᵐ v : Velocity, ∀ x : Position,
      gain (fun p => f p.2) x v = gain (fun p => g p.2) x v := by
  let : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
  have hl := ae_ae_of_ae_prod (left_quasiMeasurePreserving.ae hfg)
  have hr := ae_ae_of_ae_prod (right_quasiMeasurePreserving.ae hfg)
  filter_upwards [hl, hr] with v hlv hrv x
  apply integral_congr_ae
  filter_upwards [hlv, hrv] with p hlp hrp
  change f (scatterLeft v p.1 p.2) = g (scatterLeft v p.1 p.2) at hlp
  change f (scatterRight v p.1 p.2) = g (scatterRight v p.1 p.2) at hrp
  rw [hlp, hrp]

theorem cutoff_gain_congr {f g : Velocity → ℝ} (hfg : f =ᵐ[volume] g) (b : ℝ) :
    CollisionCutoff.gain b f =ᵐ[volume] CollisionCutoff.gain b g := by
  let : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
  have hl := ae_ae_of_ae_prod (left_quasiMeasurePreserving.ae hfg)
  have hr := ae_ae_of_ae_prod (right_quasiMeasurePreserving.ae hfg)
  filter_upwards [hl, hr] with v hlv hrv
  apply integral_congr_ae
  filter_upwards [hlv, hrv] with p hlp hrp
  change f (scatterLeft v p.1 p.2) = g (scatterLeft v p.1 p.2) at hlp
  change f (scatterRight v p.1 p.2) = g (scatterRight v p.1 p.2) at hrp
  unfold CollisionCutoff.integrand
  rw [hlp, hrp]

theorem frequency_congr {f g : Velocity → ℝ} (hfg : f =ᵐ[volume] g) (b : ℝ) (v : Velocity) :
    CollisionCutoff.frequency b f v = CollisionCutoff.frequency b g v := by
  unfold CollisionCutoff.frequency
  congr 1
  apply integral_congr_ae
  filter_upwards [hfg] with w hw
  rw [hw]

end BoltzmannNonuniqueness.CollisionNullSets

end

end

section

/-! # Weighted marginal and angular Fubini formulas on the velocity collision fiber -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness

local instance collisionFiberSFinite : SFinite ((volume : Measure Velocity).prod sphereArea) :=
  Measure.prod.instSFinite

theorem collision_fiber_test_fubini
    {r : (Velocity × Velocity) × Sphere → ℝ}
    (hi : Integrable r ((volume : Measure (Velocity × Velocity)).prod sphereArea))
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) (C : ℝ) (hC : ∀ v, |ψ v| ≤ C) :
    (∫ v : Velocity, ψ v*(∫ q : Velocity × Sphere, r ((v,q.1),q.2)
      ∂(volume : Measure Velocity).prod sphereArea)) =
    ∫ ω : Sphere, (∫ y : Velocity × Velocity, ψ y.1*r (y,ω)) ∂sphereArea := by
  let H : (Velocity × Velocity) × Sphere → ℝ := fun z => ψ z.1.1*r z
  have hI : Integrable H ((volume : Measure (Velocity × Velocity)).prod sphereArea) :=
    hi.bdd_mul (hψ.comp measurable_fst.fst).aestronglyMeasurable (ae_of_all _ (fun z => hC z.1.1))
  have hmp := measurePreserving_prodAssoc (volume : Measure Velocity) (volume : Measure Velocity) sphereArea
  have hgroup : Integrable (fun z : Velocity × (Velocity × Sphere) => ψ z.1*r ((z.1,z.2.1),z.2.2))
      ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)) := by
    have hh : Integrable H (((volume : Measure Velocity).prod volume).prod sphereArea) := by
      simpa only [Measure.volume_eq_prod] using hI
    exact hmp.symm.integrable_comp_of_integrable hh
  calc
    _ = ∫ v : Velocity, ∫ q : Velocity × Sphere, ψ v*r ((v,q.1),q.2)
        ∂(volume : Measure Velocity).prod sphereArea := by
      apply integral_congr_ae
      exact ae_of_all _ (fun v => (integral_const_mul _ _).symm)
    _ = ∫ z : Velocity × (Velocity × Sphere), ψ z.1*r ((z.1,z.2.1),z.2.2)
        ∂(volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea) :=
      (integral_prod _ hgroup).symm
    _ = ∫ z : (Velocity × Velocity) × Sphere, H z
        ∂(volume : Measure (Velocity × Velocity)).prod sphereArea := by
      have he := hmp.integral_comp MeasurableEquiv.prodAssoc.measurableEmbedding
        (fun z : Velocity × (Velocity × Sphere) => ψ z.1*r ((z.1,z.2.1),z.2.2))
      change (∫ z : (Velocity × Velocity) × Sphere, H z
        ∂((volume : Measure Velocity).prod volume).prod sphereArea) =
        ∫ z : Velocity × (Velocity × Sphere), ψ z.1*r ((z.1,z.2.1),z.2.2)
          ∂(volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea) at he
      simpa only [Measure.volume_eq_prod] using he.symm
    _ = _ := integral_prod_symm _ hI

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
