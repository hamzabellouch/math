import Mathlib
import OAI.Geometry.CubicTorus.Compactness.BVLocalTranslation

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma normalized_setIntegral_le_average (σ : FiniteMeasure Torus) (B : Set Torus)
    (g : Torus → ℝ) (hg : ∀ x, 0 ≤ g x) {r A : ℝ} (hr : 0 < r)
    (hu : (σ : Measure Torus).real B ≤ A * r ^ 2) :
    (∫ x in B, g x ∂(σ : Measure Torus)) / r ^ 2 ≤
      A * (⨍ x in B, g x ∂(σ : Measure Torus)) := by
  have hh := measure_smul_setAverage g (measure_ne_top (σ : Measure Torus) B)
  rw [smul_eq_mul] at hh
  have ha : 0 ≤ ⨍ x in B, g x ∂(σ : Measure Torus) := integral_nonneg hg
  calc
    _ = ((σ : Measure Torus).real B / r ^ 2) *
        (⨍ x in B, g x ∂(σ : Measure Torus)) := by rw [← hh]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_iff₀ (sq_pos_of_pos hr)).2 hu) ha

def normalOscillation (σ : FiniteMeasure Torus) (N : Torus → Cover) (c : Torus)
    (n : Cover) (r : ℝ) : ℝ :=
  (∫ x in Metric.closedBall c r, ‖N x - n‖ ∂(σ : Measure Torus)) / r ^ 2

lemma normalOscillation_nonneg (σ : FiniteMeasure Torus) (N : Torus → Cover)
    (c : Torus) (n : Cover) (r : ℝ) : 0 ≤ normalOscillation σ N c n r :=
  div_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) (sq_nonneg _)

theorem isMinimizerAt_normal_oscillation_ae {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Torus → Cover} (hN : Measurable N)
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) :
    ∀ᵐ c ∂(spatialNormalMeasure μ : Measure Torus),
      Tendsto (normalOscillation (spatialNormalMeasure μ) N c (N c)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨R, A, hR, _, hu⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  have hd := isMinimizerAt_normal_differentiation hV hE hmin hμ hN
    (hn.mono fun _ hx ↦ hx.le)
  filter_upwards [hd] with c hc
  apply squeeze_zero' (Eventually.of_forall (normalOscillation_nonneg _ _ _ _))
    (g := fun r ↦ (4 * A) * (⨍ x in Metric.closedBall c r,
      ‖N x - N c‖ ∂(spatialNormalMeasure μ : Measure Torus)))
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show 0 < R / 2 by positivity))]
      with r hr hrR
    have hrpos : 0 < r := hr
    have hrlt : r < R / 2 := hrR
    apply normalized_setIntegral_le_average _ _ _ (fun _ ↦ norm_nonneg _) hrpos
    have hh := (measureReal_mono
      (Metric.closedBall_subset_ball (by linarith : r < 2 * r))).trans
      (hu μ hμ c (2 * r) (by positivity) (by linarith : 2 * r ≤ R))
    calc
      _ ≤ A * (2 * r) ^ 2 := hh
      _ = _ := by ring
  · simpa only [mul_zero] using hc.const_mul (4 * A)

lemma integrable_norm_sub_normal {σ : FiniteMeasure Torus} {N : Torus → Cover}
    (hN : Measurable N) (hn : ∀ᵐ x ∂(σ : Measure Torus), ‖N x‖ = 1) (n : Cover) :
    Integrable (fun x ↦ ‖N x - n‖) (σ : Measure Torus) := by
  apply Integrable.of_bound (hN.sub_const n).norm.aestronglyMeasurable (1 + ‖n‖)
  filter_upwards [hn] with x hx
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  simpa only [hx] using norm_sub_le (N x) n

lemma directionalMass_le_normal_oscillation_integral {σ : FiniteMeasure Torus}
    {N : Torus → Cover} (hN : Measurable N)
    (hn : ∀ᵐ x ∂(σ : Measure Torus), ‖N x‖ = 1) {n a : Cover} (ha : ⟪n, a⟫ = 0)
    (B : Set Torus) :
    directionalMass σ N a B ≤ ‖a‖ * ∫ x in B, ‖N x - n‖ ∂(σ : Measure Torus) := by
  rw [← integral_const_mul]
  apply integral_mono_ae (directionalMass_integrable hN hn a).integrableOn
    ((integrable_norm_sub_normal hN hn n).const_mul _).integrableOn
  apply Eventually.of_forall
  intro x
  have hh := abs_real_inner_le_norm (N x - n) a
  rw [inner_sub_left, ha, sub_zero] at hh
  simpa only [mul_comm] using hh

lemma characteristic_tangential_translation_bound {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (c : Torus) {n v : Cover} (hv : ⟪n, v⟫ = 0) {r : ℝ} (hr : 0 < r) :
    (∫ x in Metric.ball c r,
      |characteristic E (x - quotientMap (r • v)) - characteristic E x| ∂torusVolume) / r ^ 3 ≤
      ‖v‖ * (2 + ‖v‖) ^ 2 *
        normalOscillation (spatialNormalMeasure μ) N c n ((2 + ‖v‖) * r) := by
  have hdir := characteristic_directional_translation_bound hE hμ hN hpolar hn c (r := r) hr (r • v)
  have hv' : ⟪n, r • v⟫ = 0 := by simp only [real_inner_smul_right, hv, mul_zero]
  have hosc := directionalMass_le_normal_oscillation_integral hN hn hv'
    (Metric.ball c (r + r + ‖r • v‖))
  have hnorm : ‖r • v‖ = r * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg hr.le]
  have he : r + r + ‖r • v‖ = (2 + ‖v‖) * r := by rw [hnorm]; ring
  rw [he] at hdir hosc
  have hball : (∫ x in Metric.ball c ((2 + ‖v‖) * r),
      ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in Metric.closedBall c ((2 + ‖v‖) * r),
        ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus) :=
    setIntegral_mono_set (integrable_norm_sub_normal hN hn n).integrableOn
    (Eventually.of_forall fun _ ↦ norm_nonneg _)
    (Eventually.of_forall fun _ hx ↦ Metric.ball_subset_closedBall hx)
  have hb := (hdir.trans hosc).trans (mul_le_mul_of_nonneg_left hball (norm_nonneg (r • v)))
  apply (div_le_iff₀ (pow_pos hr 3)).2
  calc
    _ ≤ ‖r • v‖ * ∫ x in Metric.closedBall c ((2 + ‖v‖) * r),
        ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus) := hb
    _ = _ := by
      rw [hnorm, normalOscillation]
      have hK : 2 + ‖v‖ ≠ 0 := ne_of_gt (by positivity)
      field_simp

theorem isMinimizerAt_tangential_blowup_ae {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) :
    ∀ᵐ c ∂(spatialNormalMeasure μ : Measure Torus), ∀ v : Cover, ⟪N c, v⟫ = 0 →
      Tendsto (fun r : ℝ ↦ (∫ x in Metric.ball c r,
        |characteristic E (x - quotientMap (r • v)) - characteristic E x| ∂torusVolume) / r ^ 3)
        (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [isMinimizerAt_normal_oscillation_ae hV hE hmin hμ hN hn] with c hc
  intro v hv
  have ht : Tendsto (fun r : ℝ ↦ (2 + ‖v‖) * r) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [mul_zero, id_eq] using ((tendsto_id : Tendsto (fun r : ℝ ↦ r) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).const_mul (2 + ‖v‖)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change 0 < (2 + ‖v‖) * r
      exact mul_pos (by positivity) hr
  apply squeeze_zero'
    (g := fun r ↦ ‖v‖ * (2 + ‖v‖) ^ 2 *
      normalOscillation (spatialNormalMeasure μ) N c (N c) ((2 + ‖v‖) * r))
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact div_nonneg (integral_nonneg fun _ ↦ abs_nonneg _) (pow_nonneg (le_of_lt hr) 3)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact characteristic_tangential_translation_bound hE hμ hN hpolar hn c hv hr
  · simpa only [Function.comp_def, mul_zero] using (hc.comp ht).const_mul (‖v‖ * (2 + ‖v‖) ^ 2)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution

namespace CubicTorus

lemma smoothApprox_nonneg {g : Cover → ℝ} (hg : ∀ x, 0 ≤ g x) (k : ℕ) (x : Cover) :
    0 ≤ smoothApprox g k x := by
  rw [smoothApprox, convolution_def]
  exact integral_nonneg fun y ↦ mul_nonneg ((mollifier k).nonneg_normed y) (hg _)

lemma flux_ordered_lower_bound {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) (hb : ∀ x, |f x| ≤ 1)
    (hf0 : ∀ x, 0 ≤ f x)
    {B : Set Torus} (hB : MeasurableSet B) (hz : ∀ x, quotientMap x ∉ B → f x = 0)
    {n a : Cover} (ha : 0 ≤ ⟪n, a⟫) :
    -(‖a‖ * ∫ x in B, ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence (fun x ↦ f x • a) x := by
  have hfa := hf.smul_const a
  rw [← normalMeasure_flux hμ hfa (fun m x ↦ by rw [hp])
    (show 0 < ‖a‖ + 1 by positivity) (fun x ↦ by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg a) (hb x)).trans (by linarith))]
  let g : Torus → ℝ := B.indicator (fun x ↦ -(‖a‖ * ‖N x - n‖))
  have hg : Measurable g := (((hN.sub_const n).norm.const_mul _).neg).indicator hB
  have hi : Integrable g (spatialNormalMeasure μ : Measure Torus) :=
    (((integrable_norm_sub_normal hN hn n).const_mul _).neg).indicator hB
  have him : Integrable (fun z : NormalBundle ↦ g (normalProjection z))
      (μ : Measure NormalBundle) :=
    (integrable_map_measure hg.aestronglyMeasurable
      normalProjection_continuous.measurable.aemeasurable).mp hi
  have hnt := (normalTest _ hfa.continuous).continuous.integrable_of_hasCompactSupport
    (μ := (μ : Measure NormalBundle)) (HasCompactSupport.of_compactSpace _)
  have hh := integral_mono_ae him hnt (show ∀ᵐ z ∂(μ : Measure NormalBundle),
      g (normalProjection z) ≤ normalTest (fun x ↦ f x • a) hfa.continuous z from by
    filter_upwards [hpolar] with z hz'
    by_cases hzB : normalProjection z ∈ B
    · simp only [g, indicator_of_mem hzB, normalTest, ContinuousMap.coe_mk,
        real_inner_smul_right]
      change -(‖a‖ * ‖N (quotientMap z.1) - n‖) ≤ f z.1 * ⟪(z.2 : Cover), a⟫
      rw [← hz']
      have hn' := (abs_le.mp (abs_real_inner_le_norm (N (quotientMap z.1) - n) a)).1
      rw [inner_sub_left] at hn'
      have hf1 := (le_abs_self (f z.1)).trans (hb z.1)
      have hnonneg := mul_nonneg (norm_nonneg a) (norm_nonneg (N (quotientMap z.1) - n))
      have hm := mul_le_mul_of_nonneg_left (show -(‖a‖ * ‖N (quotientMap z.1) - n‖) ≤
        ⟪N (quotientMap z.1), a⟫ by nlinarith) (hf0 z.1)
      nlinarith
    · simp [g, hzB, normalTest, hz z.1 hzB])
  rw [← integral_spatialNormalMeasure μ hg] at hh
  simpa only [g, integral_indicator hB, integral_neg, integral_const_mul] using hh

theorem smooth_test_ordered_translation_lower_bound {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) (hb : ∀ x, |f x| ≤ 1)
    (hf0 : ∀ x, 0 ≤ f x)
    {c : Torus} {r : ℝ} (hz : ∀ x, quotientMap x ∉ Metric.ball c r → f x = 0)
    {n a : Cover} (ha : 0 ≤ ⟪n, a⟫) :
    -(‖a‖ * ∫ x in Metric.ball c (r + ‖a‖), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (f (x + a) - f x) := by
  have hdc := hf.continuous_fderiv (by simp)
  have hd := hf.differentiable (by simp)
  have hderiv (x t) : HasDerivAt (fun s : ℝ => f (x + s • a))
      (fderiv ℝ f (x + t • a) a) t := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq, one_smul, zero_add] using
      (hd (x + t • a)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const a))
  have hFTC (x : Cover) : (∫ t in Ioc (0 : ℝ) 1, fderiv ℝ f (x + t • a) a)
      = f (x + a) - f x := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hc : Continuous (fun t : ℝ => fderiv ℝ f (x + t • a) a) :=
      (hdc.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv x t) (hc.intervalIntegrable 0 1)
  obtain ⟨M, _, hM⟩ := periodic_bounded hdc (fderiv_periodic hp)
  have hc : Continuous (fun z : Cover × ℝ => fderiv ℝ f (z.1 + z.2 • a) a) :=
    (hdc.comp (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hi : Integrable (fun z : Cover × ℝ => fderiv ℝ f (z.1 + z.2 • a) a)
      ((volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E)).prod
        (volume.restrict (Ioc (0 : ℝ) 1))) := by
    apply Integrable.of_bound hc.aestronglyMeasurable (M * ‖a‖)
    exact Filter.Eventually.of_forall fun z =>
      ((fderiv ℝ f (z.1 + z.2 • a)).le_opNorm a).trans
        (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg a))
  have ht (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      -(‖a‖ * ∫ x in Metric.ball c (r + ‖a‖), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, fderiv ℝ f (x + t • a) a := by
    let g : Cover → ℝ := fun x ↦ f (x + t • a)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp (contDiff_id.add contDiff_const)
    have hp' : ∀ n x, g (x + latticeVector n) = g x := by
      intro n x
      dsimp [g]
      rw [add_right_comm, hp]
    have hzero (x : Cover) (hx : quotientMap x ∉ Metric.ball c (r + ‖a‖)) : g x = 0 := by
      have hm : quotientMap (x + t • a) ∉ Metric.ball c r := by
        intro hx'
        apply hx
        change dist (quotientMap x) c < r + ‖a‖
        have hh := dist_triangle (quotientMap x) (quotientMap (x + t • a)) c
        have he : dist (quotientMap x) (quotientMap (x + t • a)) = ‖quotientMap (t • a)‖ := by
          rw [dist_eq_norm, quotientMap_add, sub_add_cancel_left, norm_neg]
        rw [he] at hh
        have hs : ‖t • a‖ ≤ ‖a‖ := by
          rw [norm_smul, Real.norm_of_nonneg ht.1.le]
          exact mul_le_of_le_one_left (norm_nonneg a) ht.2
        have hx'' : dist (quotientMap (x + t • a)) c < r := hx'
        linarith [norm_quotientMap_le (t • a)]
      simp [g, hz _ hm]
    have hh := flux_ordered_lower_bound hμ hN hpolar hn hg hp' (fun x ↦ hb _)
      (fun x ↦ hf0 _) Metric.isOpen_ball.measurableSet hzero ha
    simpa only [divergence_smul_const (hg.differentiable (by simp)).differentiableAt,
      g, fderiv_comp_add_right] using hh
  calc
    _ = ∫ t in Ioc (0 : ℝ) 1, -(‖a‖ * ∫ x in Metric.ball c (r + ‖a‖),
        ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) := by simp
    _ ≤ ∫ t in Ioc (0 : ℝ) 1, ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        fderiv ℝ f (x + t • a) a := by
      apply integral_mono_ae (integrable_const _) hi.integral_prod_right
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht'
      exact ht t ht'
    _ = _ := by rw [← integral_integral_swap hi]; simp_rw [hFTC]

theorem measurable_test_ordered_translation_lower_bound {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {g : Cover → ℝ} (hg : Measurable g)
    (hp : ∀ n x, g (x + latticeVector n) = g x)
    (hb : ∀ x, |g x| ≤ 1) (hg0 : ∀ x, 0 ≤ g x) {c : Torus} {r s : ℝ} (hs : 0 < s)
    (hz : ∀ x, quotientMap x ∉ Metric.ball c r → g x = 0) {n a : Cover} (ha : 0 ≤ ⟪n, a⟫) :
    -(‖a‖ * ∫ x in Metric.ball c (r + s + ‖a‖), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (g (x + a) - g x) := by
  have ht := smoothApprox_ae_tendsto hg hb
  have hta := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae ht
  have hlim : ∀ᵐ x ∂volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E),
      Tendsto (fun n => smoothApprox g n (x + a) - smoothApprox g n x)
        atTop (𝓝 (g (x + a) - g x)) := by
    apply ae_restrict_of_ae
    filter_upwards [hta, ht] with x hx hx'
    exact hx.sub hx'
  have him : ∀ n, AEStronglyMeasurable
      (fun x => smoothApprox g n (x + a) - smoothApprox g n x)
        (volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E)) := by
    intro n
    exact (((smoothApprox_contDiff hg hb n).continuous.comp
      (continuous_id.add continuous_const)).sub
        (smoothApprox_contDiff hg hb n).continuous).aestronglyMeasurable
  have hbd : ∀ n, ∀ᵐ x ∂volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E),
      ‖smoothApprox g n (x + a) - smoothApprox g n x‖ ≤ (2 : ℝ) := by
    intro n
    exact Eventually.of_forall fun x => by
      calc
        _ ≤ ‖smoothApprox g n (x + a)‖ + ‖smoothApprox g n x‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (smoothApprox_bound hb n (x + a)) (smoothApprox_bound hb n x)
        _ = 2 := by norm_num
  have hi := tendsto_integral_of_dominated_convergence (fun _ => (2 : ℝ))
    him (integrable_const 2) hbd hlim
  apply ge_of_tendsto hi
  filter_upwards [mollifier_rOut_tendsto.eventually (ge_mem_nhds hs)] with n hnr
  exact smooth_test_ordered_translation_lower_bound hμ hN hpolar hn
    (smoothApprox_contDiff hg hb n) (smoothApprox_periodic hp n) (smoothApprox_bound hb n)
    (smoothApprox_nonneg hg0 n) (fun x hx ↦ smoothApprox_zero_outside_ball hz n hnr hx) ha

lemma torus_test_ordered_translation_lower_bound {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {g : Torus → ℝ} (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1) (hg0 : ∀ x, 0 ≤ g x)
    {c : Torus} {r s : ℝ} (hs : 0 < s)
    (hz : ∀ x, x ∉ Metric.ball c r → g x = 0) {n a : Cover} (ha : 0 ≤ ⟪n, a⟫) :
    -(‖a‖ * ∫ x in Metric.ball c (r + s + ‖a‖), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in E, (g (x + quotientMap a) - g x) ∂torusVolume := by
  rw [setIntegral_lift_measurable (f := fun x => g (x + quotientMap a) - g x)
    ((hg.comp (measurable_id.add_const _)).sub hg) hE]
  have hp : ∀ n x, g (quotientMap (x + latticeVector n)) = g (quotientMap x) := by
    intro n x
    rw [quotientMap_add, quotientMap_latticeVector, add_zero]
  simpa only [Function.comp_def, quotientMap_add] using
    measurable_test_ordered_translation_lower_bound hμ hN hpolar hn (hg.comp measurable_quotientMap) hp
      (fun x => hb (quotientMap x)) (fun x ↦ hg0 _) hs (fun x hx ↦ hz _ hx) ha

def orderDefect (E : Set Torus) (a : Torus) (x : Torus) : ℝ :=
  characteristic E x * (1 - characteristic E (x - a))

lemma orderDefect_nonneg (E : Set Torus) (a x : Torus) : 0 ≤ orderDefect E a x := by
  rcases characteristic_dichotomy E x with h | h <;>
    rcases characteristic_dichotomy E (x - a) with h' | h' <;> simp [orderDefect, h, h']

lemma orderDefect_bound (E : Set Torus) (a x : Torus) : |orderDefect E a x| ≤ 1 := by
  rcases characteristic_dichotomy E x with h | h <;>
    rcases characteristic_dichotomy E (x - a) with h' | h' <;> simp [orderDefect, h, h']

lemma measurable_orderDefect {E : Set Torus} (hE : MeasurableSet E) (a : Torus) :
    Measurable (orderDefect E a) :=
  (measurable_characteristic hE).mul (measurable_const.sub
    ((measurable_characteristic hE).comp (measurable_id.sub_const _)))

theorem characteristic_ordered_translation_bound {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (c : Torus) {r s : ℝ} (hs : 0 < s) {n a : Cover} (ha : 0 ≤ ⟪n, a⟫) :
    (∫ x in Metric.ball c r, orderDefect E (quotientMap a) x ∂torusVolume) ≤
      ‖a‖ * ∫ x in Metric.ball c (r + s + ‖a‖),
        ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus) := by
  let g : Torus → ℝ := (Metric.ball c r).indicator (orderDefect E (quotientMap a))
  have hg : Measurable g := (measurable_orderDefect hE _).indicator Metric.isOpen_ball.measurableSet
  have hb (x) : |g x| ≤ 1 := by
    by_cases hx : x ∈ Metric.ball c r
    · simpa only [g, indicator_of_mem hx] using orderDefect_bound E (quotientMap a) x
    · simp [g, hx]
  have hg0 : ∀ x, 0 ≤ g x := indicator_nonneg fun _ _ ↦ orderDefect_nonneg _ _ _
  have hz (x : Torus) (hx : x ∉ Metric.ball c r) : g x = 0 := indicator_of_notMem hx _
  have hh := torus_test_ordered_translation_lower_bound hE hμ hN hpolar hn hg hb hg0 hs hz ha
  rw [integral_difference_test hE hg hb] at hh
  have heq (x) : (characteristic E (x - quotientMap a) - characteristic E x) * g x =
      -((Metric.ball c r).indicator (orderDefect E (quotientMap a)) x) := by
    by_cases hx : x ∈ Metric.ball c r
    · simp only [g, indicator_of_mem hx]
      rcases characteristic_dichotomy E x with h | h <;>
        rcases characteristic_dichotomy E (x - quotientMap a) with h' | h' <;>
          simp [orderDefect, h, h']
    · simp [g, hx]
  simp_rw [heq] at hh
  rwa [integral_neg, integral_indicator Metric.isOpen_ball.measurableSet, neg_le_neg_iff] at hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

theorem ordered_volume_product_bound {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {U W : Set Torus} (hU : MeasurableSet U) (hW : MeasurableSet W)
    (hUE : U ⊆ Eᶜ) (hWE : W ⊆ E) (c : Torus) {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 4)
    (hUB : U ⊆ Metric.ball c r) (hWB : W ⊆ Metric.ball c r) (n : Cover)
    (hordered : ∀ x ∈ U, ∀ z ∈ W, 0 ≤ ⟪n, shortestLift (z - x)⟫) :
    torusVolume.real U * torusVolume.real W ≤ 128 * r ^ 4 *
      ∫ x in Metric.ball c (4 * r), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus) := by
  let B := Metric.ball c r
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  let f : Torus × Torus → ℝ := fun z ↦ characteristic U (z.2 - z.1) * characteristic W z.2
  have hfm : Measurable f :=
    ((measurable_characteristic hU).comp (measurable_snd.sub measurable_fst)).mul
      ((measurable_characteristic hW).comp measurable_snd)
  have hfb (z : Torus × Torus) : |f z| ≤ 1 := by
    dsimp [f]
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (characteristic_bound U _)).trans
      (characteristic_bound W _)
  have hfi : Integrable f (torusVolume.prod torusVolume) :=
    Integrable.of_bound hfm.aestronglyMeasurable 1 (Eventually.of_forall hfb)
  let I : Torus → ℝ := fun a ↦ ∫ x, f (a, x) ∂torusVolume
  have hIi : Integrable I torusVolume := hfi.integral_prod_left
  have hIeq : (∫ a, I a ∂torusVolume) = torusVolume.real U * torusVolume.real W := by
    rw [show (∫ a, I a ∂torusVolume) = ∫ x, ∫ a, f (a, x) ∂torusVolume ∂torusVolume from
      integral_integral_swap hfi]
    have hinner (x : Torus) : (∫ a, f (a, x) ∂torusVolume) =
        torusVolume.real U * characteristic W x := by
      dsimp only [f]
      rw [integral_mul_const, integral_sub_left_eq_self, integral_characteristic hU.nullMeasurableSet]
      rfl
    simp_rw [hinner]
    rw [integral_const_mul, integral_characteristic hW.nullMeasurableSet]
    rfl
  have hIz (a : Torus) (ha : a ∉ Metric.ball 0 (2 * r)) : I a = 0 := by
    apply integral_eq_zero_of_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ W
    · by_cases hx' : x - a ∈ U
      · have hdist : ‖a‖ < 2 * r := by
          have hh := dist_triangle x c (x - a)
          have hxB : dist x c < r := (hWB hx)
          have hxB' : dist (x - a) c < r := (hUB hx')
          rw [dist_eq_norm, sub_sub_cancel] at hh
          rw [dist_comm c (x - a)] at hh
          linarith
        exact False.elim (ha (by simpa only [Metric.mem_ball, dist_zero_right] using hdist))
      · simp [f, characteristic, hx']
    · simp [f, characteristic, hx]
  let P := ∫ x in Metric.ball c (4 * r), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)
  have hPn : 0 ≤ P := integral_nonneg fun _ ↦ norm_nonneg _
  have hIbound (a : Torus) (ha : a ∈ Metric.ball 0 (2 * r)) : I a ≤ 2 * r * P := by
    have han : ‖a‖ < 2 * r := by simpa only [Metric.mem_ball, dist_zero_right] using ha
    by_cases hex : ∃ x : Torus, x ∈ W ∧ x - a ∈ U
    · obtain ⟨x₀, hx₀, hx₀'⟩ := hex
      have horder : 0 ≤ ⟪n, shortestLift a⟫ := by
        simpa only [sub_sub_cancel] using hordered (x₀ - a) hx₀' x₀ hx₀
      let g : Torus → ℝ := orderDefect E a
      have hgm : Measurable g := measurable_orderDefect hE a
      have hgb (x : Torus) : ‖g x‖ ≤ 1 := orderDefect_bound E a x
      have hgi : Integrable g torusVolume :=
        Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall hgb)
      have hminor (x : Torus) : f (a, x) ≤ B.indicator g x := by
        by_cases hx : x ∈ W
        · by_cases hx' : x - a ∈ U
          · have hxE : x ∈ E := hWE hx
            have hxE' : x - a ∉ E := hUE hx'
            simp [f, characteristic, hx, hx', g, B, hWB hx, hxE, hxE', orderDefect]
          · simp only [f, characteristic, indicator_of_notMem hx', zero_mul]
            exact indicator_nonneg (fun _ _ ↦ orderDefect_nonneg _ _ _) _
        · simp only [f, characteristic, indicator_of_notMem hx, mul_zero]
          exact indicator_nonneg (fun _ _ ↦ orderDefect_nonneg _ _ _) _
      have hleft : I a ≤ ∫ x in B, g x ∂torusVolume := by
        rw [← integral_indicator hB]
        apply integral_mono _ (hgi.indicator hB) hminor
        exact Integrable.of_bound (hfm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
          (Eventually.of_forall fun x ↦ hfb (a, x))
      have htrans := characteristic_ordered_translation_bound hE hμ hN hpolar hn c (r := r) hr horder
      rw [norm_shortestLift, quotientMap_shortestLift] at htrans
      have hpmono : (∫ x in Metric.ball c (r + r + ‖a‖),
          ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤ P :=
        setIntegral_mono_set (integrable_norm_sub_normal hN hn n).integrableOn
          (Eventually.of_forall fun _ ↦ norm_nonneg _) (Eventually.of_forall fun _ hx ↦
            Metric.ball_subset_ball (by linarith : r + r + ‖a‖ ≤ 4 * r) hx)
      exact hleft.trans (htrans.trans ((mul_le_mul_of_nonneg_left hpmono (norm_nonneg a)).trans
        (mul_le_mul_of_nonneg_right han.le hPn)))
    · have heq : I a = 0 := by
        apply integral_eq_zero_of_ae
        apply Eventually.of_forall
        intro x
        by_cases hx : x ∈ W
        · have hx' : x - a ∉ U := fun hx' ↦ hex ⟨x, hx, hx'⟩
          simp [f, characteristic, hx']
        · simp [f, characteristic, hx]
      rw [heq]
      positivity
  have hir : (∫ a, I a ∂torusVolume) = ∫ a in Metric.ball 0 (2 * r), I a ∂torusVolume := by
    rw [← integral_indicator Metric.isOpen_ball.measurableSet]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro a
    by_cases ha : a ∈ Metric.ball 0 (2 * r)
    · simp [ha]
    · simp [ha, hIz a ha]
  have hbound : (∫ a in Metric.ball 0 (2 * r), I a ∂torusVolume) ≤
      torusVolume.real (Metric.ball (0 : Torus) (2 * r)) * (2 * r * P) := by
    calc
      _ ≤ ∫ _ in Metric.ball 0 (2 * r), (2 * r * P) ∂torusVolume :=
        setIntegral_mono_on hIi.integrableOn (integrable_const _)
          Metric.isOpen_ball.measurableSet hIbound
      _ = _ := by simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
  have hvol : torusVolume.real (Metric.ball (0 : Torus) (2 * r)) ≤ 64 * r ^ 3 := by
    rw [Measure.real_def, volume_torusBall 0 (by positivity) (by linarith),
      ENNReal.toReal_ofReal (by positivity)]
    nlinarith [Real.pi_lt_four, pow_pos hr 3]
  rw [← hIeq, hir]
  exact hbound.trans ((mul_le_mul_of_nonneg_right hvol (by positivity)).trans (by
    dsimp [P]
    ring_nf
    exact le_rfl))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma shortestLift_quotientMap {x : Cover} (hx : ‖x‖ < 1 / 2) :
    shortestLift (quotientMap x) = x := by
  have hc : x + cubeCenter ∈ fundamentalCube := coverBall_subset_cube (by rfl)
    (by simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right] using hx)
  rw [shortestLift, ← quotientMap_add, representative_quotientMap_of_mem hc, add_sub_cancel_right]

lemma shortestLift_eq_of_lift {a : Torus} {v : Cover} (hv : quotientMap v = a)
    (hn : ‖v‖ < 1 / 2) : shortestLift a = v := by rw [← hv, shortestLift_quotientMap hn]

lemma shortestLift_sub_local {c x y : Torus} (hxy : dist x c + dist y c < 1 / 2) :
    shortestLift (x - y) = shortestLift (x - c) - shortestLift (y - c) := by
  apply shortestLift_eq_of_lift
  · simp only [quotientMap_sub, quotientMap_shortestLift]; abel
  · exact (norm_sub_le _ _).trans_lt (by
      simpa only [norm_shortestLift, ← dist_eq_norm] using hxy)

lemma dist_shortestLift_sub_local {c x y : Torus} (hxy : dist x c + dist y c < 1 / 2) :
    dist (shortestLift (x - c)) (shortestLift (y - c)) = dist x y := by
  rw [dist_eq_norm, ← shortestLift_sub_local hxy, norm_shortestLift, ← dist_eq_norm]

theorem isometryOn_shortestLift_chart (c : Torus) :
    Isometry (fun x : Metric.ball c (1 / 4) ↦ shortestLift (x.1 - c)) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  exact dist_shortestLift_sub_local (by
    have hx' : dist (x : Torus) c < 1 / 4 := x.2
    have hy' : dist (y : Torus) c < 1 / 4 := y.2
    linarith)

lemma continuousOn_shortestLift_chart (c : Torus) :
    ContinuousOn (fun x ↦ shortestLift (x - c)) (Metric.ball c (1 / 4)) :=
  (continuousOn_iff_continuous_domRestrict).mpr (isometryOn_shortestLift_chart c).continuous

lemma inner_shortestLift_sub_nonneg {c y x z : Torus} {n : Cover} (hn : ‖n‖ = 1)
    {r t : ℝ} (hyr : dist y c < r) (hxr : dist x c < t) (hzr : dist z y < t)
    (hsmall : r + 2 * t ≤ 1 / 2) (hheight : 2 * t ≤ ⟪n, shortestLift (y - c)⟫) :
    0 ≤ ⟪n, shortestLift (z - x)⟫ := by
  have he : shortestLift (z - x) = shortestLift (y - c) + shortestLift (z - y) -
      shortestLift (x - c) := by
    apply shortestLift_eq_of_lift
    · simp only [quotientMap_sub, quotientMap_add, quotientMap_shortestLift]; abel
    · have hh := (norm_sub_le (shortestLift (y - c) + shortestLift (z - y))
        (shortestLift (x - c))).trans
        (add_le_add (norm_add_le _ _) le_rfl)
      have hy' : ‖shortestLift (y - c)‖ < r := by
        simpa only [norm_shortestLift, ← dist_eq_norm] using hyr
      have hz' : ‖shortestLift (z - y)‖ < t := by
        simpa only [norm_shortestLift, ← dist_eq_norm] using hzr
      have hx' : ‖shortestLift (x - c)‖ < t := by
        simpa only [norm_shortestLift, ← dist_eq_norm] using hxr
      linarith
  rw [he, inner_sub_right, inner_add_right]
  have hx := abs_real_inner_le_norm n (shortestLift (x - c))
  have hz := abs_real_inner_le_norm n (shortestLift (z - y))
  simp only [hn, one_mul, norm_shortestLift, ← dist_eq_norm, abs_le] at hx hz
  linarith [hx.2, hz.1]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma ordered_density_normal_oscillation {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {c a b : Torus} {n : Cover} (hnorm : ‖n‖ = 1)
    {r t δ : ℝ} (hr : 0 < r) (hsmall : r ≤ 1 / 16) (ht : 0 < t) (htr : t ≤ r)
    (hδ : 0 < δ) (ha : dist a c < r) (hb : dist b c < r)
    (hda : δ * t ^ 3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a t))
    (hdb : δ * t ^ 3 ≤ torusVolume.real (E ∩ Metric.ball b t))
    (hheight : 2 * t ≤ ⟪n, shortestLift (b - a)⟫) :
    δ ^ 2 * (t / r) ^ 6 ≤ 131072 * normalOscillation (spatialNormalMeasure μ) N c n (8 * r) := by
  have hba : dist b a < 2 * r := by linarith [dist_triangle b c a, dist_comm c a]
  have hUB : Eᶜ ∩ Metric.ball a t ⊆ Metric.ball c (2 * r) := by
    intro x hx
    have hh : dist x a < t := hx.2
    exact show dist x c < 2 * r from by linarith [dist_triangle x a c]
  have hWB : E ∩ Metric.ball b t ⊆ Metric.ball c (2 * r) := by
    intro x hx
    have hh : dist x b < t := hx.2
    exact show dist x c < 2 * r from by linarith [dist_triangle x b c]
  have hsep : ∀ x ∈ Eᶜ ∩ Metric.ball a t, ∀ z ∈ E ∩ Metric.ball b t,
      0 ≤ ⟪n, shortestLift (z - x)⟫ := by
    intro x hx z hz
    exact inner_shortestLift_sub_nonneg hnorm hba hx.2 hz.2 (by linarith) hheight
  have hp := ordered_volume_product_bound hE hμ hN hpolar hn
    (hE.compl.inter Metric.isOpen_ball.measurableSet) (hE.inter Metric.isOpen_ball.measurableSet)
    inter_subset_left inter_subset_left c (by positivity : 0 < 2 * r) (by linarith) hUB hWB n hsep
  have hprod := mul_le_mul hda hdb (by positivity : 0 ≤ δ * t ^ 3) ENNReal.toReal_nonneg
  have hm : (∫ x in Metric.ball c (4 * (2 * r)),
      ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in Metric.closedBall c (8 * r), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus) := by
    rw [show 4 * (2 * r) = 8 * r by ring]
    exact setIntegral_mono_set (integrable_norm_sub_normal hN hn n).integrableOn
      (Eventually.of_forall fun _ ↦ norm_nonneg _)
      (Eventually.of_forall fun _ hx ↦ Metric.ball_subset_closedBall hx)
  have hh := hprod.trans (hp.trans (mul_le_mul_of_nonneg_left hm (by positivity)))
  apply (mul_le_mul_iff_left₀ (pow_pos hr 6)).mp
  calc
    δ ^ 2 * (t / r) ^ 6 * r ^ 6 = (δ * t ^ 3) * (δ * t ^ 3) := by field_simp
    _ ≤ 128 * (2 * r) ^ 4 * ∫ x in Metric.closedBall c (8 * r),
        ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus) := hh
    _ = (131072 * normalOscillation (spatialNormalMeasure μ) N c n (8 * r)) * r ^ 6 := by
      rw [normalOscillation]
      field_simp
      ring

def BoundaryFlatAt (B : Set Torus) (c : Torus) (n : Cover) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ y ∈ B,
    dist y c < r → |⟪n, shortestLift (y - c)⟫| < ε * r

lemma normal_oscillation_implies_boundary_flatness {E B : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hd : ∀ a ∈ B, ∀ t : ℝ, 0 < t → t ≤ R →
      δ * t ^ 3 ≤ torusVolume.real (E ∩ Metric.ball a t) ∧
      δ * t ^ 3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a t))
    {c : Torus} (hc : c ∈ B) {n : Cover} (hnorm : ‖n‖ = 1)
    (hlim : Tendsto (normalOscillation (spatialNormalMeasure μ) N c n) (𝓝[>] 0) (𝓝 0)) :
    BoundaryFlatAt B c n := by
  intro ε hε
  let η := min ε 1
  have hη : 0 < η := lt_min hε zero_lt_one
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηε : η ≤ ε := min_le_left _ _
  have hthreshold : 0 < δ ^ 2 * (η / 4) ^ 6 := by positivity
  have hevent : ∀ᶠ s : ℝ in 𝓝[>] 0,
      131072 * normalOscillation (spatialNormalMeasure μ) N c n s < δ ^ 2 * (η / 4) ^ 6 :=
    (show Tendsto (fun s ↦ 131072 * normalOscillation (spatialNormalMeasure μ) N c n s)
      (𝓝[>] 0) (𝓝 0) from by simpa only [mul_zero] using hlim.const_mul 131072).eventually
        (Iio_mem_nhds hthreshold)
  filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_min hR (by norm_num : (0 : ℝ) < 1 / 16))),
      eventually_nhdsGT_zero_mul_left (by norm_num : (0 : ℝ) < 8) hevent] with r hr hrsmall hos
  have hrpos : 0 < r := hr
  have hrR : r ≤ R := (show r < min R (1 / 16) from hrsmall).le.trans (min_le_left _ _)
  have hr16 : r ≤ 1 / 16 := (show r < min R (1 / 16) from hrsmall).le.trans (min_le_right _ _)
  let t := η * r / 4
  have ht : 0 < t := by dsimp [t]; positivity
  have htr : t ≤ r := by dsimp [t]; nlinarith
  have htR : t ≤ R := htr.trans hrR
  have hquot : t / r = η / 4 := by dsimp [t]; field_simp
  have hforbid : ∀ a ∈ B, dist a c < r → ∀ b ∈ B, dist b c < r →
      ¬ 2 * t ≤ ⟪n, shortestLift (b - a)⟫ := by
    intro a ha har b hb hbr hh
    have hh' := ordered_density_normal_oscillation hE hμ hN hpolar hn hnorm hrpos hr16 ht htr
      hδ har hbr (hd a ha t ht htR).2 (hd b hb t ht htR).1 hh
    rw [hquot] at hh'
    exact (not_lt_of_ge hh') hos
  intro y hy hyr
  have hcc : dist c c < r := by simpa only [dist_self] using hrpos
  have hl : ⟪n, shortestLift (y - c)⟫ < 2 * t := lt_of_not_ge (hforbid c hc hcc y hy hyr)
  have he : shortestLift (c - y) = -shortestLift (y - c) := by
    apply shortestLift_eq_of_lift
    · rw [quotientMap_neg, quotientMap_shortestLift]; abel
    · rw [norm_neg, norm_shortestLift, ← dist_eq_norm]
      linarith
  have hk := lt_of_not_ge (hforbid y hy hyr c hc hcc)
  rw [he, inner_neg_right] at hk
  have habs : |⟪n, shortestLift (y - c)⟫| < 2 * t := abs_lt.mpr ⟨by linarith, hl⟩
  apply habs.trans_le
  dsimp [t]
  nlinarith

theorem isMinimizerAt_boundary_flat_ae {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) :
    ∀ᵐ c ∂(spatialNormalMeasure μ : Measure Torus),
      BoundaryFlatAt (frontier (openRepresentative E)) c (N c) := by
  obtain ⟨R, δ, hR, hδ, hd⟩ := isMinimizerAt_two_sided_density hV hE hmin
  have hsupp := Measure.support_mem_ae (μ := (spatialNormalMeasure μ : Measure Torus))
  have hflat := isMinimizerAt_normal_oscillation_ae hV hE hmin hμ hN hn
  filter_upwards [hsupp, hn, hflat] with c hc hnc hl
  rw [isMinimizerAt_frontier_openRepresentative hV hE hmin]
  exact normal_oscillation_implies_boundary_flatness hE hμ hN hpolar hn hR hδ hd
    (spatialNormalMeasure_support_subset_boundary hE hμ hc) hnc hl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

def normalCap (c : Torus) (n : Cover) (r h : ℝ) : Set Torus :=
  {x | dist x c < r ∧ h < ⟪n, shortestLift (x - c)⟫}

lemma normalCap_eq_image (c : Torus) (n : Cover) {r : ℝ} (hr : r ≤ 1 / 2) (h : ℝ) :
    normalCap c n r h = (fun v ↦ quotientMap v + c) ''
      (Metric.ball (0 : Cover) r ∩ {v | h < ⟪n, v⟫}) := by
  ext x
  constructor
  · rintro ⟨hx, hh⟩
    refine ⟨shortestLift (x - c), ⟨?_, hh⟩, ?_⟩
    · simpa only [Metric.mem_ball, dist_zero_right, norm_shortestLift, ← dist_eq_norm] using hx
    · simp only [quotientMap_shortestLift]; abel
  · rintro ⟨v, ⟨hv, hh⟩, rfl⟩
    have hv' : ‖v‖ < 1 / 2 := (show ‖v‖ < r by simpa using hv).trans_le hr
    simp only [normalCap, Set.mem_ofPred_eq, add_sub_cancel_right,
      shortestLift_quotientMap hv']
    refine ⟨?_, hh⟩
    rw [dist_eq_norm, add_sub_cancel_right, ← norm_shortestLift, shortestLift_quotientMap hv']
    simpa using hv

lemma isPreconnected_normalCap (c : Torus) (n : Cover) {r : ℝ} (hr : r ≤ 1 / 2) (h : ℝ) :
    IsPreconnected (normalCap c n r h) := by
  rw [normalCap_eq_image c n hr h]
  have hc : Convex ℝ {v : Cover | h < ⟪n, v⟫} :=
    (convex_Ioi h).linear_preimage (innerSL ℝ n).toLinearMap
  exact ((convex_ball (0 : Cover) r).inter hc).isPreconnected.image _
    (continuous_quotientMap.add continuous_const).continuousOn

lemma preconnected_avoids_frontier {U S : Set Torus} (hU : IsOpen U)
    (hS : IsPreconnected S) (h : Disjoint S (frontier U)) :
    S ⊆ U ∨ S ⊆ (closure U)ᶜ := by
  apply hS.subset_or_subset hU isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_right (compl_subset_compl.mpr subset_closure))
  intro x hx
  by_cases hxU : x ∈ U
  · exact Or.inl hxU
  · right
    intro hxcl
    exact Set.disjoint_left.mp h hx (by rw [frontier, hU.interior_eq]; exact ⟨hxcl, hxU⟩)

lemma normalCap_avoids_frontier {U : Set Torus} {c : Torus} {n : Cover} {r ε : ℝ}
    (hflat : ∀ y ∈ frontier U, dist y c < r →
      |⟪n, shortestLift (y - c)⟫| < ε * r) :
    Disjoint (normalCap c n r (ε * r)) (frontier U) := by
  rw [Set.disjoint_left]
  intro y hy hb
  exact (not_lt_of_ge (le_abs_self _)) ((hflat y hb hy.1).trans hy.2)

lemma normalCap_ball_subset {c : Torus} {n : Cover} (hn : ‖n‖ = 1)
    {r ε : ℝ} (hr : 0 < r) (hs : r ≤ 1 / 16) (hε : ε ≤ 1 / 4) :
    Metric.ball (quotientMap ((r / 2) • n) + c) (r / 8) ⊆ normalCap c n r (ε * r) := by
  let b := quotientMap ((r / 2) • n) + c
  have hrn : ‖(r / 2) • n‖ = r / 2 := by rw [norm_smul, hn, mul_one, Real.norm_of_nonneg (by positivity)]
  have hbc : dist b c = r / 2 := by
    rw [dist_eq_norm, show b - c = quotientMap ((r / 2) • n) by dsimp [b]; abel,
      ← norm_shortestLift, shortestLift_quotientMap (by rw [hrn]; linarith), hrn]
  intro x hx
  have hxb : dist x b < r / 8 := hx
  have hxc : dist x c < r := by linarith [dist_triangle x b c]
  refine ⟨hxc, ?_⟩
  have hl : shortestLift (x - c) = shortestLift (x - b) + (r / 2) • n := by
    apply shortestLift_eq_of_lift
    · simp only [quotientMap_add, quotientMap_shortestLift]; dsimp [b]; abel
    · have hh := norm_add_le (shortestLift (x - b)) ((r / 2) • n)
      rw [norm_shortestLift, ← dist_eq_norm, hrn] at hh
      linarith
  rw [hl, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hn]
  have hh := (abs_real_inner_le_norm n (shortestLift (x - b)))
  rw [hn, one_mul, norm_shortestLift, ← dist_eq_norm, abs_le] at hh
  have hm := mul_le_mul_of_nonneg_right hε hr.le
  nlinarith [hh.1]

lemma small_oscillation_outward_cap {E U : Set Torus} (hE : MeasurableSet E)
    (hU : IsOpen U) (hUE : U =ᵐ[torusVolume] E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover}
    (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {c : Torus} {n : Cover} (hnorm : ‖n‖ = 1) {r ε δ : ℝ}
    (hr : 0 < r) (hs : r ≤ 1 / 16) (hε : ε ≤ 1 / 4) (hδ : 0 < δ)
    (hden : δ * (r / 8) ^ 3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball c (r / 8)))
    (hflat : ∀ y ∈ frontier U, dist y c < r →
      |⟪n, shortestLift (y - c)⟫| < ε * r)
    (hosc : 131072 * normalOscillation (spatialNormalMeasure μ) N c n (8 * r) <
      δ ^ 2 * (1 / 8) ^ 6) :
    normalCap c n r (ε * r) ⊆ (closure U)ᶜ := by
  rcases preconnected_avoids_frontier hU (isPreconnected_normalCap c n (by linarith) _)
    (normalCap_avoids_frontier hflat) with hi | ho
  · exfalso
    let b := quotientMap ((r / 2) • n) + c
    have hbU : Metric.ball b (r / 8) ⊆ U := (normalCap_ball_subset hnorm hr hs hε).trans hi
    have heq : torusVolume.real (E ∩ Metric.ball b (r / 8)) =
        torusVolume.real (Metric.ball b (r / 8)) := by
      calc
        _ = torusVolume.real (U ∩ Metric.ball b (r / 8)) :=
          measureReal_congr (hUE.symm.inter EventuallyEq.rfl)
        _ = _ := by rw [inter_eq_right.mpr hbU]
    have hvol : torusVolume.real (Metric.ball b (r / 8)) =
        torusVolume.real (Metric.ball c (r / 8)) := by
      simp only [Measure.real_def, volume_torusBall _ (by positivity : 0 ≤ r / 8) (by linarith)]
    have hdb : δ * (r / 8) ^ 3 ≤ torusVolume.real (E ∩ Metric.ball b (r / 8)) := by
      rw [heq, hvol]
      exact hden.trans (measureReal_mono inter_subset_right)
    have hrn : ‖(r / 2) • n‖ = r / 2 := by
      rw [norm_smul, hnorm, mul_one, Real.norm_of_nonneg (by positivity)]
    have hbc : shortestLift (b - c) = (r / 2) • n := by
      rw [show b - c = quotientMap ((r / 2) • n) by dsimp [b]; abel]
      exact shortestLift_quotientMap (by rw [hrn]; linarith)
    have hdist : dist b c < r := by
      rw [dist_eq_norm, ← norm_shortestLift, hbc, hrn]; linarith
    have hheight : 2 * (r / 8) ≤ ⟪n, shortestLift (b - c)⟫ := by
      rw [hbc, inner_smul_right, real_inner_self_eq_norm_sq, hnorm]; nlinarith
    have hh := ordered_density_normal_oscillation hE hμ hN hpolar hn hnorm hr hs
      (by positivity : 0 < r / 8) (by linarith) hδ
      (by simpa only [dist_self] using hr) hdist hden hdb hheight
    have hquot : (r / 8) / r = 1 / 8 := by field_simp
    rw [hquot] at hh
    exact (not_lt_of_ge hh) hosc
  · exact ho

theorem isMinimizerAt_outward_cap_ae {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) :
    ∀ᵐ c ∂(spatialNormalMeasure μ : Measure Torus),
      ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in 𝓝[>] 0,
        normalCap c (N c) r (ε * r) ⊆ (closure (openRepresentative E))ᶜ := by
  obtain ⟨R, δ, hR, hδ, hd⟩ := isMinimizerAt_two_sided_density hV hE hmin
  filter_upwards [isMinimizerAt_boundary_flat_ae hV hE hmin hμ hN hpolar hn,
      isMinimizerAt_normal_oscillation_ae hV hE hmin hμ hN hn,
      Measure.support_mem_ae (μ := (spatialNormalMeasure μ : Measure Torus)), hn]
    with c hc hl hsupp hnc
  have hcb := spatialNormalMeasure_support_subset_boundary hE hμ hsupp
  intro ε hε
  let η := min ε (1 / 4)
  have hη : 0 < η := lt_min hε (by norm_num)
  have hevent : ∀ᶠ s : ℝ in 𝓝[>] 0,
      131072 * normalOscillation (spatialNormalMeasure μ) N c (N c) s < δ ^ 2 * (1 / 8) ^ 6 :=
    (show Tendsto (fun s ↦ 131072 * normalOscillation (spatialNormalMeasure μ) N c (N c) s)
      (𝓝[>] 0) (𝓝 0) from by simpa only [mul_zero] using hl.const_mul 131072).eventually
        (Iio_mem_nhds (by positivity))
  filter_upwards [hc η hη, self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_min hR (by norm_num : (0 : ℝ) < 1 / 16))),
      eventually_nhdsGT_zero_mul_left (by norm_num : (0 : ℝ) < 8) hevent]
    with r hflat hr hrsmall hosc
  have hrpos : 0 < r := hr
  have hrR : r ≤ R := (show r < min R (1 / 16) from hrsmall).le.trans (min_le_left _ _)
  have hr16 : r ≤ 1 / 16 := (show r < min R (1 / 16) from hrsmall).le.trans (min_le_right _ _)
  have hh := small_oscillation_outward_cap hE (isOpen_openRepresentative E)
    (isMinimizerAt_openRepresentative_ae hV hE hmin) hμ hN hpolar hn hnc hrpos hr16
    (min_le_right ε (1 / 4)) hδ (hd c hcb (r / 8) (by positivity) (by linarith)).2 hflat hosc
  intro y hy
  exact hh ⟨hy.1, (mul_le_mul_of_nonneg_right (min_le_left ε (1 / 4)) hrpos.le).trans_lt hy.2⟩

lemma polar_reverse_normal {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) :
    ∀ᵐ z ∂((μ.map reverseNormal) : Measure NormalBundle),
      -N (quotientMap z.1) = (z.2 : Cover) := by
  change ∀ᵐ z ∂Measure.map reverseNormal (μ : Measure NormalBundle), _
  apply (ae_map_iff continuous_reverseNormal.measurable.aemeasurable
    (show MeasurableSet {z : NormalBundle | -N (quotientMap z.1) = (z.2 : Cover)} from
      measurableSet_eq_fun
        (hN.comp (measurable_quotientMap.comp (continuous_subtype_val.comp continuous_fst).measurable)).neg
        (continuous_subtype_val.comp continuous_snd).measurable)).2
  filter_upwards [hpolar] with z hz
  change -N (quotientMap z.1) = -(z.2 : Cover)
  rw [hz]

def HalfspaceTrappedAt (U : Set Torus) (c : Torus) (n : Cover) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in 𝓝[>] 0,
    normalCap c n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap c (-n) r (ε * r) ⊆ U

theorem isMinimizerAt_halfspace_trapped_ae {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) :
    ∀ᵐ c ∂(spatialNormalMeasure μ : Measure Torus),
      HalfspaceTrappedAt (openRepresentative E) c (N c) := by
  have hVc : 1 - V ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2], by linarith [hV.1]⟩
  have hm : IsMinimizerAt (1 - V) Eᶜ :=
    (isMinimizerAt_compl ⟨hV.1.le, hV.2.le⟩).2 hmin
  have hnc : ∀ᵐ x ∂(spatialNormalMeasure (μ.map reverseNormal) : Measure Torus),
      ‖-N x‖ = 1 := by simpa only [spatialNormalMeasure_reverse, norm_neg] using hn
  have hout := isMinimizerAt_outward_cap_ae hV hE hmin hμ hN hpolar hn
  have hin := isMinimizerAt_outward_cap_ae hVc hE.compl hm (isNormalMeasure_compl hE hμ)
    hN.neg (polar_reverse_normal hN hpolar) hnc
  rw [spatialNormalMeasure_reverse] at hin
  have he : (closure (openRepresentative Eᶜ))ᶜ = openRepresentative E := by
    rw [isMinimizerAt_closure_openRepresentative hVc hE.compl hm]
    rfl
  filter_upwards [hout, hin] with c hc hd
  intro ε hε
  filter_upwards [hc ε hε, hd ε hε] with r hr hs
  exact ⟨hr, he ▸ hs⟩

end CubicTorus

end
end

end

end OAI
