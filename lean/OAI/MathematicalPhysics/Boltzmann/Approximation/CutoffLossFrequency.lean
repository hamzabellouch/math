import OAI.MathematicalPhysics.Boltzmann.Branching.HotQuadraticGain
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionWeakMarginals
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticDensityMeasurable

namespace OAI

section

/-! # The cutoff collision terms are dominated by the physical collision marginals -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

def cutoffLossDensity (b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  ∫ q : Velocity × Sphere, CollisionCutoff.kernel b p.2 q.1 q.2*f p*f (p.1,q.1)
    ∂((volume : Measure Velocity).prod sphereArea)

theorem cutoffLossDensity_measurable {f : X × Velocity → ℝ} (hf : Measurable f) (b : ℝ) :
    Measurable (cutoffLossDensity b f) := by
  have hk : Measurable (fun z : (X × Velocity) × (Velocity × Sphere) =>
      CollisionCutoff.kernel b z.1.2 z.2.1 z.2.2) := by
    unfold CollisionCutoff.kernel
    exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      (by unfold collisionKernel normalComponent; fun_prop) measurable_const
  have hm : Measurable (fun z : (X × Velocity) × (Velocity × Sphere) =>
      CollisionCutoff.kernel b z.1.2 z.2.1 z.2.2*f z.1*f (z.1.1,z.2.1)) := by
    exact (hk.mul (hf.comp measurable_fst)).mul
      (hf.comp (measurable_fst.fst.prodMk measurable_snd.fst))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

omit [MeasurableSpace X] in
theorem cutoffLossDensity_nonneg {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (b : ℝ) (p : X × Velocity) : 0 ≤ cutoffLossDensity b f p :=
  integral_nonneg (fun _q => mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg b _ _ _)
    (hf _)) (hf _))

omit [MeasurableSpace X] in
theorem cutoffGainDensity_nonneg {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (b : ℝ) (p : X × Velocity) : 0 ≤ KineticCollisionNullSets.gain b f p :=
  integral_nonneg (fun _q => mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg b _ _ _)
    (hf _)) (hf _))

theorem cutoff_gainLoss_le {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hpair : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity)))) (b : ℝ) :
    ∀ᵐ p ∂μ.prod (volume : Measure Velocity),
      KineticCollisionNullSets.gain b f p ≤ gainDensity f p ∧
      cutoffLossDensity b f p ≤ lossDensity f p := by
  have hp : Integrable
      (fun z : (X × Velocity) × (Velocity × Sphere) => postRate f (collisionGrouping.symm z))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) :=
    (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
      (postRate_integrable hfm hf hpair)
  have hl : Integrable
      (fun z : (X × Velocity) × (Velocity × Sphere) => preRate f (collisionGrouping.symm z))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) :=
    (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
      (preRate_integrable hfm hf hpair)
  filter_upwards [hp.prod_right_ae,hl.prod_right_ae] with p hpi hli
  constructor
  · apply integral_mono_of_nonneg (ae_of_all _ (fun q =>
      mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg b _ _ _) (hf _)) (hf _))) hpi
    filter_upwards [] with q
    rw [postRate_formula]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (CollisionCutoff.kernel_le b _ _ _) (hf _)) (hf _)
  · apply integral_mono_of_nonneg (ae_of_all _ (fun q =>
      mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg b _ _ _) (hf _)) (hf _))) hli
    filter_upwards [] with q
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (CollisionCutoff.kernel_le b _ _ _) (hf _)) (hf _)

theorem cutoff_gainLoss_uniformIntegrable {μ : Measure X} [SFinite μ]
    {f : ℕ → X × Velocity → ℝ} (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hpair : ∀ n, Integrable (pairDensity (f n)) (μ.prod (volume : Measure (Velocity × Velocity))))
    (hgain : UniformIntegrable (fun n => gainDensity (f n)) 1 (μ.prod (volume : Measure Velocity)))
    (hloss : UniformIntegrable (fun n => lossDensity (f n)) 1 (μ.prod (volume : Measure Velocity)))
    (b : ℕ → ℝ) :
    UniformIntegrable (fun n => KineticCollisionNullSets.gain (b n) (f n)) 1
      (μ.prod (volume : Measure Velocity)) ∧
    UniformIntegrable (fun n => cutoffLossDensity (b n) (f n)) 1
      (μ.prod (volume : Measure Velocity)) := by
  have hb (n) := cutoff_gainLoss_le (hfm n) (hf n) (hpair n) (b n)
  exact ⟨uniformIntegrable_mono_nonneg hgain
      (fun n => (KineticCollisionNullSets.measurable_gain (hfm n) (b n)).aestronglyMeasurable)
      (fun n => ae_of_all _ (cutoffGainDensity_nonneg (hf n) (b n)))
      (fun n => (hb n).mono (fun _ h => h.1)),
    uniformIntegrable_mono_nonneg hloss
      (fun n => (cutoffLossDensity_measurable (hfm n) (b n)).aestronglyMeasurable)
      (fun n => ae_of_all _ (cutoffLossDensity_nonneg (hf n) (b n)))
      (fun n => (hb n).mono (fun _ h => h.2))⟩

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The cap-sized quadratic hot gain contributes only O(r²) after dilation -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem cutoff_hot_gain_bound (hcarleman : Published.GPV2009CarlemanInput)
    {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (b : ℝ) {f : X × Velocity → ℝ}
    (hf : Measurable f) (hfn : ∀ z, 0 ≤ f z) (hftwo : ∀ z, f z ≤ 2) (x : X) :
    ∀ᵐ v : Velocity,
      KineticCollisionNullSets.gain b (fun z => H q z.2*f z) (x,v) ≤
        (4*HotApplication.realBound q)*H q v := by
  have hm : Measurable (fun v => H q v*f (x,v)) :=
    (ChartKernel.measurable_H q).mul (hf.comp (measurable_const.prodMk measurable_id))
  have hn (v) : 0 ≤ H q v*f (x,v) := mul_nonneg (H_nonneg q v) (hfn _)
  have hb (v) : H q v*f (x,v) ≤ 2*H q v :=
    (mul_le_mul_of_nonneg_left (hftwo _) (H_nonneg q v)).trans_eq (mul_comm _ _)
  filter_upwards [HotRealGain.dominated_gain hcarleman hq₁ hq₂ hm hn hb] with v hv
  exact (CollisionCutoff.gain_le b hm hn v 0 hv.1).trans (by
    simpa only [show (2:ℝ)^2=4 by norm_num] using hv.2 0)

theorem normalized_cutoff_hot_gain_bound (hcarleman : Published.GPV2009CarlemanInput)
    {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (b : ℝ) {f : X × Velocity → ℝ}
    (hf : Measurable f) (hfn : ∀ z, 0 ≤ f z) (hftwo : ∀ z, f z ≤ 2) (x : X) :
    ∀ᵐ v : Velocity,
      KineticCollisionNullSets.gain b (fun z => H q z.2*f z) (x,v)/H q v ≤
        4*HotApplication.realBound q := by
  filter_upwards [cutoff_hot_gain_bound hcarleman hq₁ hq₂ b hf hfn hftwo x] with v hv
  exact (div_le_iff₀ (H_pos q v)).mpr hv

theorem quadratic_hot_error_tendsto_zero {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) (q : ℝ) :
    Tendsto (fun n => (r n)^2*(4*HotApplication.realBound q)) atTop (𝓝 0) := by
  simpa only [zero_pow (by norm_num : 2 ≠ 0),zero_mul] using
    (hr.pow 2).mul_const (4*HotApplication.realBound q)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Identification of the cutoff loss marginal with collision frequency -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

theorem integral_cutoffKernel (b : ℝ) (v w : Velocity) :
    (∫ ω : Sphere, CollisionCutoff.kernel b v w ω ∂sphereArea) =
      2*Real.pi*CollisionCutoff.rate b v w := by
  unfold CollisionCutoff.kernel CollisionCutoff.rate
  by_cases h : ‖v-w‖ < b
  · simp only [ite_eq_left h,integral_collisionKernel_sphereArea]
  · simp only [ite_eq_right h,integral_zero,mul_zero]

omit [MeasurableSpace X] in
theorem cutoffLossDensity_eq_frequency (b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity)
    (hi : Integrable (fun q : Velocity × Sphere =>
      CollisionCutoff.kernel b p.2 q.1 q.2*f p*f (p.1,q.1))
      ((volume : Measure Velocity).prod sphereArea)) :
    cutoffLossDensity b f p = f p*KineticCollisionNullSets.frequency b f p := by
  unfold cutoffLossDensity
  rw [integral_prod _ hi]
  simp_rw [integral_mul_const,integral_cutoffKernel]
  calc
    _ = ∫ w : Velocity, (f p*(2*Real.pi))*(CollisionCutoff.rate b p.2 w*f (p.1,w)) := by
      apply integral_congr_ae
      filter_upwards [] with w
      ring
    _ = _ := by
      rw [integral_const_mul]
      unfold KineticCollisionNullSets.frequency CollisionCutoff.frequency
      ring

theorem cutoff_loss_ae_eq_frequency {μ : Measure X} [SFinite μ]
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hpair : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity)))) (b : ℝ) :
    cutoffLossDensity b f =ᵐ[μ.prod (volume : Measure Velocity)]
      fun p => f p*KineticCollisionNullSets.frequency b f p := by
  have hl : Integrable
      (fun z : (X × Velocity) × (Velocity × Sphere) => preRate f (collisionGrouping.symm z))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) :=
    (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
      (preRate_integrable hfm hf hpair)
  filter_upwards [hl.prod_right_ae] with p hp
  apply cutoffLossDensity_eq_frequency
  have hS : MeasurableSet {q : Velocity × Sphere | ‖p.2-q.1‖ < b} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hi := hp.indicator hS
  convert hi using 1
  funext q
  by_cases h : ‖p.2-q.1‖ < b
  · rw [Set.indicator_of_mem (show q ∈ {q : Velocity × Sphere | ‖p.2-q.1‖ < b} from h)]
    simp only [CollisionCutoff.kernel,ite_eq_left h]
    rfl
  · rw [Set.indicator_of_notMem (show q ∉ {q : Velocity × Sphere | ‖p.2-q.1‖ < b} from h)]
    simp only [CollisionCutoff.kernel,ite_eq_right h,zero_mul]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
