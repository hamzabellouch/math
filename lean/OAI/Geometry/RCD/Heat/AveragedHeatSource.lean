import OAI.Geometry.RCD.Heat.HeatMeasureEvolution
import OAI.Geometry.RCD.Heat.KernelMeasureBounds
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace OAI

/-!
# Averaged measure-source heat identity including time zero

The average of the positive kernel over a fixed finite-volume set is
bounded by its reciprocal volume, uniformly at all positive times.
This bounds its pairing with any finite signed measure. The genuine L2
heat flow gives continuity at zero, so the source identity extends to the
initial endpoint without a pointwise kernel limit.
-/

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)

include hp in
theorem kernelAverage_bounds {t : ℝ} (ht : 0 < t) (A : Set X) (z : X) :
    0 ≤ kernelAverage μ p t A z ∧ kernelAverage μ p t A z ≤ (μ.real A)⁻¹ := by
  have he : (∫ a in A, p t a z ∂μ) = ∫ a in A, p t z a ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun a => hp.symmetric t ht a z
  have hlo : 0 ≤ ∫ a in A, p t z a ∂μ := integral_nonneg fun a => hp.nonneg t ht z a
  have hup : (∫ a in A, p t z a ∂μ) ≤ 1 := by
    calc
      _ ≤ ∫ a, p t z a ∂μ := setIntegral_le_integral (hp.integrable t ht z)
        (Eventually.of_forall fun a => hp.nonneg t ht z a)
      _ = 1 := hp.mass_one t ht z
  dsimp only [kernelAverage]
  rw [he]
  constructor
  · exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) hlo
  · have hn : 0 ≤ (μ.real A)⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
    exact (mul_le_mul_of_nonneg_left hup hn).trans_eq (mul_one _)

include hp in
theorem kernelAverage_eq_kernelHeat {t : ℝ} (ht : 0 < t)
    (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞) (z : X) :
    kernelAverage μ p t A z =
      kernelHeat μ hQ hp t (uniformDensityLp μ A hA hAt) z := by
  rw [kernelHeat, real_inner_comm, uniformDensityLp, inner_smul_left,
    L2.inner_indicatorConstLp_one]
  dsimp only [kernelAverage, Measure.real]
  congr 1
  apply integral_congr_ae
  filter_upwards [(heatKernelRow_coe μ hQ hp ht z).filter_mono ae_restrict_le] with a ha
  exact (hp.symmetric t ht a z).trans ha.symm

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [μ.Regular] in
/-- The normalized indicator is genuinely integrable on any finite-volume
set, including the zero-volume case. -/
theorem uniformDensityLp_integrable (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞) :
    Integrable (uniformDensityLp μ A hA hAt) μ := by
  have hi : IntegrableOn (fun _ : X => (μ A).toReal⁻¹) A μ := integrableOn_const hAt
  have hi' : Integrable (A.indicator (fun _ : X => (μ A).toReal⁻¹)) μ :=
    (integrable_indicator_iff hA).mpr hi
  exact hi'.congr (uniformDensityLp_ae μ A hA hAt).symm

include hp in
theorem kernelAverage_heatSobolev_coe {t : ℝ} (ht : 0 < t)
    (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞) :
    SobolevSpace.toLp μ hQ (heatSobolev μ hQ t ht (uniformDensityLp μ A hA hAt)) =ᵐ[μ]
      kernelAverage μ p t A := by
  rw [heatSobolev_toLp]
  filter_upwards [(kernelHeat_represents μ hQ hp ht (uniformDensityLp μ A hA hAt)
    (uniformDensityLp_integrable μ A hA hAt)).symm] with z hz
  exact hz.trans (kernelAverage_eq_kernelHeat μ hQ hp ht A hA hAt z).symm

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [μ.Regular] in
/-- Pairing with the normalized indicator is exactly the actual set average. -/
theorem uniformDensityLp_inner (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞)
    (f : Lp ℝ 2 μ) :
    ⟪uniformDensityLp μ A hA hAt, f⟫_ℝ = (μ.real A)⁻¹ * ∫ x in A, f x ∂μ := by
  rw [uniformDensityLp, inner_smul_left, L2.inner_indicatorConstLp_one]
  rfl

include hp in
/-- The weak derivative of the average pairs the actual averaged kernel
with the full signed source. -/
theorem IsMeasureLaplacian.average_heat_hasDerivAt
    {u : SobolevSpace μ hQ} {ν : SignedMeasure X}
    (hν : IsMeasureLaplacian μ hQ u ν) (c : X) {R : ℝ} (hR : 0 < R)
    (hu : ∀ᵐ x ∂μ, R < dist c x → SobolevSpace.toLp μ hQ u x = 0)
    (hsν : ν.variation (Metric.closedBall c R)ᶜ = 0)
    (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ⟪heatAt μ hQ s (uniformDensityLp μ A hA hAt),
      SobolevSpace.toLp μ hQ u⟫_ℝ)
      (∫ᵛ z, kernelAverage μ p t A z ∂<•ν) t := by
  have he := hν.test_continuous μ hQ c hR hu hsν
    (heatSobolev μ hQ t ht (uniformDensityLp μ A hA hAt))
    (show Continuous (kernelAverage μ p t A) from by
      have hfun : kernelAverage μ p t A = kernelHeat μ hQ hp t (uniformDensityLp μ A hA hAt) :=
        funext (kernelAverage_eq_kernelHeat μ hQ hp ht A hA hAt)
      rw [hfun]
      exact kernelHeat_continuous μ hQ hp ht _)
    (kernelAverage_heatSobolev_coe μ hQ hp ht A hA hAt)
  have hd := heatAt_inner_lp_hasDerivAt μ hQ (uniformDensityLp μ A hA hAt) u t ht
  rw [energyForm_comm μ hQ, he, neg_neg] at hd
  exact hd

include hp in
/-- The averaged identity extends to time zero. The bound on the average
kernel makes the full signed source absolutely integrable in time. -/
theorem IsMeasureLaplacian.average_heat_sub_eq_integral
    {u : SobolevSpace μ hQ} {ν : SignedMeasure X}
    (hν : IsMeasureLaplacian μ hQ u ν) (c : X) {R : ℝ} (hR : 0 < R)
    (hu : ∀ᵐ x ∂μ, R < dist c x → SobolevSpace.toLp μ hQ u x = 0)
    (hsν : ν.variation (Metric.closedBall c R)ᶜ = 0)
    (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (μ.real A)⁻¹ * (∫ x in A, heatAt μ hQ t (SobolevSpace.toLp μ hQ u) x ∂μ) -
      (μ.real A)⁻¹ * (∫ x in A, heatAt μ hQ s (SobolevSpace.toLp μ hQ u) x ∂μ) =
      ∫ r in s..t, (∫ᵛ z, kernelAverage μ p r A z ∂<•ν) := by
  let F := fun r => ⟪heatAt μ hQ r (uniformDensityLp μ A hA hAt), SobolevSpace.toLp μ hQ u⟫_ℝ
  let D := fun r => ∫ᵛ z, kernelAverage μ p r A z ∂<•ν
  have hd (r : ℝ) (hr : 0 < r) : HasDerivAt F (D r) r :=
    hν.average_heat_hasDerivAt μ hQ hp c hR hu hsν A hA hAt hr
  have heae : deriv F =ᵐ[volume.restrict (Ioc s t)] D := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (hd r (hs.trans_lt hr.1)).deriv
  have hDm : AEStronglyMeasurable D (volume.restrict (Ioc s t)) :=
    (aestronglyMeasurable_deriv F _).congr heae
  let : IsFiniteMeasure ν.variation := by
    rw [← ν.totalVariation_eq_variation]
    infer_instance
  let C := (μ.real A)⁻¹ * ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip‖ * ν.variation.real univ
  have hDb : ∀ᵐ r ∂volume.restrict (Ioc s t), ‖D r‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    apply VectorMeasure.norm_integral_le_of_norm_le_const
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (kernelAverage_bounds μ hQ hp (hs.trans_lt hr.1) A z).1]
      exact (kernelAverage_bounds μ hQ hp (hs.trans_lt hr.1) A z).2
  have hDi : IntervalIntegrable D volume s t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact IntegrableOn.of_bound measure_Ioc_lt_top hDm C hDb
  have hFc : Continuous F := (heatAt_continuous μ hQ _).inner continuous_const
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hFc.continuousOn
    (fun r hr => hd r (hs.trans_lt hr.1)) hDi
  rw [he]
  have hF (r : ℝ) : F r = (μ.real A)⁻¹ * ∫ x in A, heatAt μ hQ r (SobolevSpace.toLp μ hQ u) x ∂μ := by
    dsimp only [F]
    rw [heatAt_inner, uniformDensityLp_inner]
  rw [hF t, hF s]

include hp in
/-- The initial-endpoint form needed for the ball Gram comparison. -/
theorem IsMeasureLaplacian.average_heat_sub_initial
    {u : SobolevSpace μ hQ} {ν : SignedMeasure X}
    (hν : IsMeasureLaplacian μ hQ u ν) (c : X) {R : ℝ} (hR : 0 < R)
    (hu : ∀ᵐ x ∂μ, R < dist c x → SobolevSpace.toLp μ hQ u x = 0)
    (hsν : ν.variation (Metric.closedBall c R)ᶜ = 0)
    (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞)
    {t : ℝ} (ht : 0 ≤ t) :
    (μ.real A)⁻¹ * (∫ x in A, heatAt μ hQ t (SobolevSpace.toLp μ hQ u) x ∂μ) -
      (μ.real A)⁻¹ * (∫ x in A, SobolevSpace.toLp μ hQ u x ∂μ) =
      ∫ r in 0..t, (∫ᵛ z, kernelAverage μ p r A z ∂<•ν) := by
  simpa only [heatAt_zero, one_apply_eq_self] using
    hν.average_heat_sub_eq_integral μ hQ hp c hR hu hsν A hA hAt (s := 0) le_rfl ht

include hp in
/-- Exact short/long source decomposition for comparing a ball average
with a point heat value. Bounds may be applied separately to the short-time
average and the long-time kernel difference; singular mass is retained. -/
theorem IsMeasureLaplacian.average_initial_sub_point_heat
    {u : SobolevSpace μ hQ} {ν : SignedMeasure X}
    (hν : IsMeasureLaplacian μ hQ u ν) (c : X) {R : ℝ} (hR : 0 < R)
    (hu : ∀ᵐ x ∂μ, R < dist c x → SobolevSpace.toLp μ hQ u x = 0)
    (hsν : ν.variation (Metric.closedBall c R)ᶜ = 0)
    (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (x : X) :
    (μ.real A)⁻¹ * (∫ z in A, SobolevSpace.toLp μ hQ u z ∂μ) -
      kernelHeat μ hQ hp s (SobolevSpace.toLp μ hQ u) x =
      ((μ.real A)⁻¹ * (∫ z in A, heatAt μ hQ t (SobolevSpace.toLp μ hQ u) z ∂μ) -
        kernelHeat μ hQ hp t (SobolevSpace.toLp μ hQ u) x) -
      (∫ r in 0..s, (∫ᵛ z, kernelAverage μ p r A z ∂<•ν)) -
      (∫ r in s..t, (∫ᵛ z, kernelAverage μ p r A z ∂<•ν)) +
      (∫ r in s..t, (∫ᵛ z, p r x z ∂<•ν)) := by
  have h0 := hν.average_heat_sub_initial μ hQ hp c hR hu hsν A hA hAt hs.le
  have hA := hν.average_heat_sub_eq_integral μ hQ hp c hR hu hsν A hA hAt hs.le hst
  have hx := hν.kernelHeat_sub_eq_integral μ hQ hp c hR hu hsν hs hst x
  linarith

end RegularPointCoordinates

end

end OAI
