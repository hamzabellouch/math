import OAI.Geometry.Perimeter.Regularity.FlatExcess
import OAI.Geometry.Perimeter.Regularity.FiberHeight
import OAI.Geometry.Perimeter.Regularity.HalfspaceHorizontal

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap

theorem integral_phase_error_mul {n : ℕ} {E H : Set (Euc n)}
    (hE : MeasurableSet E) (hH : MeasurableSet H) {g : Euc n → ℝ}
    (hg : Integrable g volume) :
    (∫ x, (E.indicator (fun _ ↦ (1:ℝ)) x - H.indicator (fun _ ↦ (1:ℝ)) x) * g x) =
      (∫ x in E, g x) - ∫ x in H, g x := by
  have heq : (fun x ↦ (E.indicator (fun _ ↦ (1:ℝ)) x -
      H.indicator (fun _ ↦ (1:ℝ)) x) * g x) = E.indicator g - H.indicator g := by
    funext x
    by_cases hxE : x ∈ E <;> by_cases hxH : x ∈ H <;> simp [hxE,hxH]
  rw [heq]
  change (∫ x, E.indicator g x - H.indicator g x) = _
  rw [integral_sub (hg.indicator hE) (hg.indicator hH),
    integral_indicator hE, integral_indicator hH]

theorem integrable_phase_error_mul {n : ℕ} {E H : Set (Euc n)}
    (hE : MeasurableSet E) (hH : MeasurableSet H) {g : Euc n → ℝ}
    (hg : Integrable g volume) :
    Integrable (fun x ↦ (E.indicator (fun _ ↦ (1:ℝ)) x -
      H.indicator (fun _ ↦ (1:ℝ)) x) * g x) volume := by
  convert (hg.indicator hE).sub (hg.indicator hH) using 1
  funext x
  by_cases hxE : x ∈ E <;> by_cases hxH : x ∈ H <;> simp [hxE,hxH]

theorem cutoffPhaseError_distribution {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v w : Euc n} (_hv : ‖v‖ = 1) (hw : inner ℝ v w = 0)
    {η φ : Euc n → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hφ : ContDiff ℝ ∞ φ) {R : ℝ} (hR : 0 < R)
    (hs : tsupport η ⊆ Metric.ball 0 R) :
    -(∫ x, cutoffPhaseError E v η x * fderiv ℝ φ x w) =
      (∫ x, (E.indicator (fun _ ↦ (1:ℝ)) x -
        {z | inner ℝ v z < 0}.indicator (fun _ ↦ (1:ℝ)) x) *
          (φ x * fderiv ℝ η x w)) -
      ∫ x in Metric.ball 0 R, φ x * (η x * inner ℝ (approximateNormal E x) w)
        ∂perimeterMeasure E := by
  let H : Set (Euc n) := {x | inner ℝ v x < 0}
  have heH : H = {x | inner ℝ x v < 0} := by ext x; simp only [H, real_inner_comm]
  have hHm : MeasurableSet H := (isOpen_lt (continuous_const.inner continuous_id)
    continuous_const).measurableSet
  have hηd := hη.differentiable (by simp)
  have hφd := hφ.differentiable (by simp)
  have hdi : Integrable (fun x ↦ η x * fderiv ℝ φ x w) volume :=
    (hη.continuous.mul ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      hc.mul_right
  have hdi' : Integrable (fun x ↦ φ x * fderiv ℝ η x w) volume :=
    (hφ.continuous.mul ((hη.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ w).mul_left
  have hprod (x : Euc n) : fderiv ℝ (fun y ↦ η y * φ y) x w =
      η x * fderiv ℝ φ x w + φ x * fderiv ℝ η x w := by
    rw [fderiv_fun_mul (hηd x) (hφd x)]
    rfl
  have hgg : (∫ x in E, fderiv ℝ (fun y ↦ η y * φ y) x w) =
      ∫ x in Metric.ball 0 R, φ x * (η x * inner ℝ (approximateNormal E x) w)
        ∂perimeterMeasure E := by
    rw [← divergence_scalar_direction ((hη.mul hφ).differentiable (by simp)) w,
      minimizing_gaussGreen_local hn hmin (Metric.ball 0 R) Metric.isOpen_ball
        (hmin.2.1 0 R hR).ne (fun y ↦ (η y * φ y) • w) ((hη.mul hφ).smul contDiff_const)
        hc.mul_right.smul_right
        (tsupport_smul_subset_left _ _ |>.trans (tsupport_mul_subset_left.trans hs))]
    apply integral_congr_ae
    exact ae_of_all _ fun x ↦ by simp only [real_inner_smul_right]; ring
  have hzero : (∫ x in H, fderiv ℝ (fun y ↦ η y * φ y) x w) = 0 := by
    rw [heH]
    exact halfspace_horizontal_integral hw (hη.mul hφ) hc.mul_right
  simp_rw [hprod] at hgg hzero
  rw [integral_add hdi.integrableOn hdi'.integrableOn] at hgg hzero
  have hleft : (∫ x, cutoffPhaseError E v η x * fderiv ℝ φ x w) =
      (∫ x in E, η x * fderiv ℝ φ x w) - ∫ x in H, η x * fderiv ℝ φ x w := by
    rw [← integral_phase_error_mul hmin.1 hHm hdi]
    apply integral_congr_ae
    exact ae_of_all _ fun x ↦ by unfold cutoffPhaseError; dsimp [H]; ring
  rw [hleft, integral_phase_error_mul hmin.1 hHm hdi']
  linarith

theorem cutoffPhaseError_convolution_fderiv {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v w : Euc n} (hv : ‖v‖ = 1) (hw : inner ℝ v w = 0)
    {η k : Euc n → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hk : ContDiff ℝ ∞ k) (hck : HasCompactSupport k) {R : ℝ} (hR : 0 < R)
    (hs : tsupport η ⊆ Metric.ball 0 R) (x : Euc n) :
    fderiv ℝ (cutoffPhaseError E v η ⋆[lsmul ℝ ℝ, volume] k) x w =
      ((fun y ↦ (E.indicator (fun _ ↦ (1:ℝ)) y -
        {z | inner ℝ v z < 0}.indicator (fun _ ↦ (1:ℝ)) y) * fderiv ℝ η y w)
          ⋆[lsmul ℝ ℝ, volume] k) x -
      ((fun y ↦ η y * inner ℝ (approximateNormal E y) w)
        ⋆[lsmul ℝ ℝ, (perimeterMeasure E).restrict (Metric.ball 0 R)] k) x := by
  let f := cutoffPhaseError E v η
  have hfi : Integrable f volume := by
    have hi := integrable_phase_error_mul (H := {z | inner ℝ v z < 0}) hmin.1
      ((isOpen_lt (continuous_const.inner continuous_id) continuous_const).measurableSet)
      (hη.continuous.integrable_of_hasCompactSupport hc)
    change Integrable (fun y ↦ η y * (E.indicator (fun _ ↦ (1:ℝ)) y -
      {z | inner ℝ v z < 0}.indicator (fun _ ↦ (1:ℝ)) y)) volume
    simpa only [mul_comm] using hi
  let φ : Euc n → ℝ := fun y ↦ k (x-y)
  have hφ : ContDiff ℝ ∞ φ := hk.comp (contDiff_const.sub contDiff_id)
  have hd (y : Euc n) : fderiv ℝ φ y w = -fderiv ℝ k (x-y) w := by
    have h := ((hk.differentiable (by simp) (x-y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))).fderiv
    simpa only [φ, Function.comp_def, sub_apply, zero_apply, id_apply,
      zero_sub, ContinuousLinearMap.comp_apply, neg_apply, map_neg] using
      congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L w) h
  have hdconv : fderiv ℝ (f ⋆[lsmul ℝ ℝ, volume] k) x w =
      -(∫ y, f y * fderiv ℝ φ y w) := by
    rw [(hck.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hfi.locallyIntegrable
      (hk.of_le (by simp)) x).fderiv,
      convolution_precompR_apply (lsmul ℝ ℝ) hfi.locallyIntegrable (hck.fderiv ℝ)
        (hk.continuous_fderiv (by simp))]
    simp_rw [hd, mul_neg]
    rw [integral_neg, neg_neg]
    rfl
  rw [hdconv, cutoffPhaseError_distribution hn hmin hv hw hη hc hφ hR hs]
  congr 1 <;> apply integral_congr_ae <;> exact ae_of_all _ fun y ↦ by
    change _ = _ * k (x-y)
    dsimp [φ]
    ring

theorem integral_abs_convolution_le {n : ℕ} (μ : Measure (Euc n)) [SFinite μ]
    {f k : Euc n → ℝ} (hf : Integrable f μ) (hk : Integrable k volume) :
    (∫ x, |(f ⋆[lsmul ℝ ℝ, μ] k) x|) ≤
      (∫ y, |f y| ∂μ) * ∫ x, |k x| := by
  have hi := (hf.convolution_integrand (lsmul ℝ ℝ) hk).integral_prod_left
  have hi' := (hf.abs.convolution_integrand (lsmul ℝ ℝ) hk.abs).integral_prod_left
  calc
    _ ≤ ∫ x, ((fun y ↦ |f y|) ⋆[lsmul ℝ ℝ, μ] (fun y ↦ |k y|)) x := by
      apply integral_mono hi.abs hi'
      intro x
      change |∫ y, f y * k (x-y) ∂μ| ≤ ∫ y, |f y| * |k (x-y)| ∂μ
      simpa only [abs_mul] using (abs_integral_le_integral_abs (f := fun y ↦ f y * k (x-y)) (μ := μ))
    _ = _ := integral_convolution (lsmul ℝ ℝ) hf.abs hk.abs

theorem smooth_directional_translation_lintegral_le {n : ℕ} {u : Euc n → ℝ}
    (hu : ContDiff ℝ 1 u) (a : Euc n) :
    (∫⁻ x, ‖u (x+a)-u x‖ₑ) ≤ ∫⁻ x, ‖fderiv ℝ u x a‖ₑ := by
  have hfd := hu.continuous_fderiv one_ne_zero
  have hpoint (x : Euc n) : ‖u (x+a)-u x‖ₑ ≤
      ∫⁻ t in Ioc (0:ℝ) 1, ‖fderiv ℝ u (x+t•a) a‖ₑ := by
    have hd (t : ℝ) : HasDerivAt (fun s : ℝ ↦ u (x+s•a))
        (fderiv ℝ u (x+t•a) a) t := by
      simpa only [Function.comp_def, id_eq, one_smul] using
        (hu.differentiable one_ne_zero (x+t•a)).hasFDerivAt.comp_hasDerivAt t
          (HasDerivAt.const_add x ((hasDerivAt_id t).smul_const a))
    have hi : IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ u (x+t•a) a) volume 0 1 :=
      ((hfd.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
        continuous_const).intervalIntegrable _ _
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t) hi
    simp only [one_smul, zero_smul, add_zero] at he
    rw [← he, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact enorm_integral_le_lintegral_enorm _
  have hm : Measurable (fun p : Euc n × ℝ ↦ ‖fderiv ℝ u (p.1+p.2•a) a‖ₑ) :=
    ((hfd.comp (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply
      continuous_const).enorm.measurable
  calc
    _ ≤ ∫⁻ x, ∫⁻ t in Ioc (0:ℝ) 1, ‖fderiv ℝ u (x+t•a) a‖ₑ := lintegral_mono hpoint
    _ = ∫⁻ t in Ioc (0:ℝ) 1, ∫⁻ x, ‖fderiv ℝ u (x+t•a) a‖ₑ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ t in Ioc (0:ℝ) 1, ∫⁻ x, ‖fderiv ℝ u x a‖ₑ := by
      apply lintegral_congr
      intro t
      exact lintegral_add_right_eq_self (fun x : Euc n ↦ ‖fderiv ℝ u x a‖ₑ) (t•a)
    _ = _ := by simp

theorem minimizing_normal_scalar_integrable {n : ℕ} {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) {η : Euc n → ℝ}
    (hη : Continuous η) (hc : HasCompactSupport η) (w : Euc n)
    {c : Euc n} {R : ℝ} (hR : 0 < R) :
    Integrable (fun x ↦ η x * inner ℝ (approximateNormal E x) w)
      ((perimeterMeasure E).restrict (Metric.ball c R)) := by
  let μ := (perimeterMeasure E).restrict (Metric.ball c R)
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 c R hR⟩
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hη
  have hM0 : 0 ≤ M := (norm_nonneg (η c)).trans (hM c)
  apply Integrable.of_bound
    (hη.aestronglyMeasurable.mul
      ((measurable_approximateNormal hmin.1).inner measurable_const).aestronglyMeasurable)
    (M*‖w‖)
  apply ae_of_all μ
  intro x
  change ‖η x * inner ℝ (approximateNormal E x) w‖ ≤ _
  rw [norm_mul]
  have hb : ‖inner ℝ (approximateNormal E x) w‖ ≤ ‖w‖ :=
    (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (approximateNormal_norm_le_one E x) (norm_nonneg w))
  exact mul_le_mul (hM x) hb (norm_nonneg _) hM0

theorem cutoffPhaseError_convolution_variation_le {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v w : Euc n} (hv : ‖v‖ = 1) (hw : inner ℝ v w = 0)
    {η k : Euc n → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hk : ContDiff ℝ ∞ k) (hck : HasCompactSupport k) {R : ℝ} (hR : 0 < R)
    (hs : tsupport η ⊆ Metric.ball 0 R) :
    (∫ x, |fderiv ℝ (cutoffPhaseError E v η ⋆[lsmul ℝ ℝ, volume] k) x w|) ≤
      ((∫ x, |(E.indicator (fun _ ↦ (1:ℝ)) x -
        {z | inner ℝ v z < 0}.indicator (fun _ ↦ (1:ℝ)) x) * fderiv ℝ η x w|) +
      ∫ x in Metric.ball 0 R, |η x * inner ℝ (approximateNormal E x) w|
        ∂perimeterMeasure E) * ∫ x, |k x| := by
  let μ := (perimeterMeasure E).restrict (Metric.ball 0 R)
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 0 R hR⟩
  let g : Euc n → ℝ := fun x ↦ (E.indicator (fun _ ↦ (1:ℝ)) x -
    {z | inner ℝ v z < 0}.indicator (fun _ ↦ (1:ℝ)) x) * fderiv ℝ η x w
  let q : Euc n → ℝ := fun x ↦ η x * inner ℝ (approximateNormal E x) w
  have hg : Integrable g volume := integrable_phase_error_mul hmin.1
    (isOpen_lt (continuous_const.inner continuous_id) continuous_const).measurableSet
    (((hη.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ w))
  have hq : Integrable q μ := minimizing_normal_scalar_integrable hmin hη.continuous hc w hR
  have hki : Integrable k volume := hk.continuous.integrable_of_hasCompactSupport hck
  have hgk : Integrable (g ⋆[lsmul ℝ ℝ, volume] k) volume :=
    (hg.convolution_integrand (lsmul ℝ ℝ) hki).integral_prod_left
  have hqk : Integrable (q ⋆[lsmul ℝ ℝ, μ] k) volume :=
    (hq.convolution_integrand (lsmul ℝ ℝ) hki).integral_prod_left
  simp_rw [cutoffPhaseError_convolution_fderiv hn hmin hv hw hη hc hk hck hR hs]
  calc
    _ ≤ (∫ x, |(g ⋆[lsmul ℝ ℝ, volume] k) x|) +
        ∫ x, |(q ⋆[lsmul ℝ ℝ, μ] k) x| := by
      rw [← integral_add hgk.abs hqk.abs]
      apply integral_mono (hgk.sub hqk).abs (hgk.abs.add hqk.abs)
      intro x
      exact abs_sub _ _
    _ ≤ (∫ x, |g x|) * (∫ x, |k x|) + (∫ x, |q x| ∂μ) * ∫ x, |k x| :=
      add_le_add (integral_abs_convolution_le volume hg hki) (integral_abs_convolution_le μ hq hki)
    _ = _ := by rw [← add_mul]

theorem localizedPhaseError_integrable {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (v : Euc n) (R : ℝ) :
    Integrable (localizedPhaseError E v R) volume := by
  rw [localizedPhaseError, integrable_indicator_iff measurableSet_ball]
  apply (integrableOn_const measure_ball_lt_top.ne (C := (1:ℝ))).mono'
    (((measurable_const.indicator hE).sub
      (measurable_const.indicator (isOpen_lt (continuous_const.inner continuous_id)
        continuous_const).measurableSet)).aestronglyMeasurable.restrict)
  exact ae_of_all _ fun x ↦ by
    by_cases hxE : x ∈ E <;> by_cases hxH : inner ℝ v x < 0 <;> simp [hxE,hxH]

theorem phase_error_cutoff_derivative_le {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (v w : Euc n)
    {η : Euc n → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    {R L : ℝ} (hs : tsupport η ⊆ Metric.ball 0 R) (hL : 0 ≤ L)
    (hgrad : ∀ x ∈ Metric.ball 0 R, ‖gradient η x‖ ≤ L) :
    (∫ x, |(E.indicator (fun _ ↦ (1:ℝ)) x -
      {z | inner ℝ v z < 0}.indicator (fun _ ↦ (1:ℝ)) x) * fderiv ℝ η x w|) ≤
      (L * ‖w‖) * ∫ x, |localizedPhaseError E v R x| := by
  have hi := integrable_phase_error_mul (H := {z | inner ℝ v z < 0}) hE
    (isOpen_lt (continuous_const.inner continuous_id) continuous_const).measurableSet
    (((hη.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ w))
  rw [← integral_const_mul]
  apply integral_mono hi.abs ((localizedPhaseError_integrable hE v R).abs.const_mul _)
  intro x
  dsimp only
  by_cases hx : x ∈ Metric.ball (0:Euc n) R
  · have hd : |fderiv ℝ η x w| ≤ L * ‖w‖ := by
      have he : ‖gradient η x‖ = ‖fderiv ℝ η x‖ :=
        (InnerProductSpace.toDual ℝ (Euc n)).symm.norm_map _
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (he ▸ hgrad x hx) (norm_nonneg _))
    rw [abs_mul]
    simpa only [localizedPhaseError, indicator_of_mem hx, mul_comm] using
      mul_le_mul_of_nonneg_left hd
        (abs_nonneg (E.indicator (fun _ ↦ (1:ℝ)) x -
          {z | inner ℝ v z < 0}.indicator (fun _ ↦ (1:ℝ)) x))
  · have hn : x ∉ tsupport η := fun h ↦ hx (hs h)
    rw [fderiv_of_notMem_tsupport ℝ hn]
    simp only [zero_apply, mul_zero, abs_zero]
    positivity

theorem cutoffPhaseError_convolution_height_variation {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v w : Euc n} (hv : ‖v‖ = 1) (hw : inner ℝ v w = 0)
    {η k : Euc n → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hk : ContDiff ℝ ∞ k) (hck : HasCompactSupport k) {R : ℝ} (hR : 0 < R)
    (hs : tsupport η ⊆ Metric.ball 0 R)
    {a L : ℝ} (ha : 0 ≤ a) (hL : 0 ≤ L)
    (hheight : ∀ x ∈ perimeterSupport E ∩ Metric.ball 0 R, |inner ℝ v x| ≤ a)
    (hgrad : ∀ x ∈ Metric.ball 0 R, ‖gradient η x‖ ≤ L)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x < 0)) :
    (∫ x, |fderiv ℝ (cutoffPhaseError E v η ⋆[lsmul ℝ ℝ, volume] k) x w|) ≤
      (‖w‖ * a * L * (volume.real (Metric.ball (0:Euc n) (2*R)) / R +
        2 * (perimeter E (Metric.ball 0 R)).toReal)) * ∫ x, |k x| := by
  have herr : (∫ x, |localizedPhaseError E v R x|) ≤
      a * (volume.real (Metric.ball (0:Euc n) (2*R)) / R) := by
    have hi := slab_integral_bound (localizedPhaseError_measurable hmin.1 v R) hv ha hR
      (show Function.support (localizedPhaseError E v R) ⊆ Metric.ball 0 R from
        support_indicator_subset)
      (localizedPhaseError_slab_bound E v R a hphase)
    simp only [Real.norm_eq_abs] at hi
    have ht : 0 < 2*R := by positivity
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hR).mpr
    nlinarith
  have hn' := minimizing_horizontal_normal_integral_le hn hmin 0 hv hw 0 hR hη hc hs
    ha hL (by simpa only [sub_zero] using hheight) hgrad
  have hg := phase_error_cutoff_derivative_le hmin.1 v w hη hc hs hL hgrad
  have hg' := hg.trans (mul_le_mul_of_nonneg_left herr (by positivity : 0 ≤ L*‖w‖))
  have hb := add_le_add hg' hn'
  have hb' : ((∫ x, |(E.indicator (fun _ ↦ (1:ℝ)) x -
      {z | inner ℝ v z < 0}.indicator (fun _ ↦ (1:ℝ)) x) * fderiv ℝ η x w|) +
      ∫ x in Metric.ball 0 R, |η x * inner ℝ (approximateNormal E x) w| ∂perimeterMeasure E) ≤
      ‖w‖ * a * L * (volume.real (Metric.ball (0:Euc n) (2*R)) / R +
        2 * (perimeter E (Metric.ball 0 R)).toReal) := by
    exact hb.trans_eq (by ring)
  exact (cutoffPhaseError_convolution_variation_le hn hmin hv hw hη hc hk hck hR hs).trans
    (mul_le_mul_of_nonneg_right hb' (integral_nonneg fun x ↦ abs_nonneg _))

theorem translation_lintegral_le_of_mollifier_direction_bound {n : ℕ}
    {f : Euc n → ℝ} (hf : LocallyIntegrable f volume) (hc : HasCompactSupport f)
    (a : Euc n) (B : ℝ)
    (hb : ∀ j, (∫ x, |fderiv ℝ (c1Mollify f j) x a|) ≤ B) :
    (∫⁻ x, ‖f (x+a)-f x‖ₑ) ≤ ENNReal.ofReal B := by
  let u : ℕ → Euc n → ℝ := c1Mollify f
  have hu : ∀ j, ContDiff ℝ ∞ (u j) := fun j ↦
    (c1Mollifier j).hasCompactSupport_normed.contDiff_convolution_left _
      (c1Mollifier j).contDiff_normed hf
  have hcu : ∀ j, HasCompactSupport (u j) := fun j ↦ c1Mollify_hasCompactSupport hc j
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun j ↦ u j x) atTop (𝓝 (f x)) := by
    apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      c1Mollifier_radius_tendsto (K := 2) _ hf
    apply Eventually.of_forall
    intro j
    dsimp [c1Mollifier]
    linarith
  have hlimadd : ∀ᵐ x ∂volume, Tendsto (fun j ↦ u j (x+a)) atTop (𝓝 (f (x+a))) :=
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae hlim
  have hlimnorm : ∀ᵐ x ∂volume, Tendsto (fun j ↦ ‖u j (x+a)-u j x‖ₑ) atTop
      (𝓝 (‖f (x+a)-f x‖ₑ)) := by
    filter_upwards [hlimadd,hlim] with x hx hy
    exact (hx.sub hy).enorm
  calc
    _ = ∫⁻ x, liminf (fun j ↦ ‖u j (x+a)-u j x‖ₑ) atTop := by
      apply lintegral_congr_ae
      filter_upwards [hlimnorm] with x hx using hx.liminf_eq.symm
    _ ≤ liminf (fun j ↦ ∫⁻ x, ‖u j (x+a)-u j x‖ₑ) atTop :=
      lintegral_liminf_le' (fun j ↦ (((hu j).continuous.comp
        (continuous_id.add continuous_const)).sub (hu j).continuous).enorm.measurable.aemeasurable)
    _ ≤ _ := by
      have hj : ∀ j, (∫⁻ x, ‖u j (x+a)-u j x‖ₑ) ≤ ENNReal.ofReal B := by
        intro j
        apply (smooth_directional_translation_lintegral_le ((hu j).of_le (by simp)) a).trans
        have hid : Integrable (fun x ↦ fderiv ℝ (u j) x a) volume :=
          (((hu j).continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
            ((hcu j).fderiv_apply ℝ a)
        rw [← ofReal_integral_norm_eq_lintegral_enorm hid]
        apply ENNReal.ofReal_le_ofReal
        simpa only [Real.norm_eq_abs] using hb j
      exact liminf_le_of_frequently_le (Eventually.of_forall hj).frequently

theorem cutoffPhaseError_horizontal_translation_le {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v w : Euc n} (hv : ‖v‖ = 1) (hw : inner ℝ v w = 0)
    {η : Euc n → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    {R : ℝ} (hR : 0 < R) (hs : tsupport η ⊆ Metric.ball 0 R)
    {a L : ℝ} (ha : 0 ≤ a) (hL : 0 ≤ L)
    (hheight : ∀ x ∈ perimeterSupport E ∩ Metric.ball 0 R, |inner ℝ v x| ≤ a)
    (hgrad : ∀ x ∈ Metric.ball 0 R, ‖gradient η x‖ ≤ L)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x < 0)) :
    (∫⁻ x, ‖cutoffPhaseError E v η (x+w)-cutoffPhaseError E v η x‖ₑ) ≤
      ENNReal.ofReal (‖w‖ * a * L * (volume.real (Metric.ball (0:Euc n) (2*R)) / R +
        2 * (perimeter E (Metric.ball 0 R)).toReal)) := by
  let f := cutoffPhaseError E v η
  have hfi : Integrable f volume := by
    have hi := integrable_phase_error_mul (H := {z | inner ℝ v z < 0}) hmin.1
      ((isOpen_lt (continuous_const.inner continuous_id) continuous_const).measurableSet)
      (hη.continuous.integrable_of_hasCompactSupport hc)
    change Integrable (fun y ↦ η y * (E.indicator (fun _ ↦ (1:ℝ)) y -
      {z | inner ℝ v z < 0}.indicator (fun _ ↦ (1:ℝ)) y)) volume
    simpa only [mul_comm] using hi
  have hcf : HasCompactSupport f := hc.mul_right
  apply translation_lintegral_le_of_mollifier_direction_bound hfi.locallyIntegrable hcf
  intro j
  have hflip : (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip = lsmul ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    exact mul_comm b a
  have heq : c1Mollify f j = f ⋆[lsmul ℝ ℝ, volume] (c1Mollifier j).normed volume := by
    change (c1Mollifier j).normed volume ⋆[lsmul ℝ ℝ, volume] f = _
    rw [← convolution_flip, hflip]
  rw [heq]
  have hk1 : (∫ x, |(c1Mollifier (n := n) j).normed volume x|) = 1 := by
    simp_rw [abs_of_nonneg ((c1Mollifier j).nonneg_normed _)]
    exact (c1Mollifier j).integral_normed
  have hh := cutoffPhaseError_convolution_height_variation (k := (c1Mollifier j).normed volume) hn hmin hv hw hη hc
    (c1Mollifier j).contDiff_normed (c1Mollifier j).hasCompactSupport_normed hR hs
    ha hL hheight hgrad hphase
  simpa only [hk1, mul_one] using hh

end RPISingularHarnack

end

end OAI
