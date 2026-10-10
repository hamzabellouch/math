import OAI.Geometry.Perimeter.Regularity.FlatExcess

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap

def phaseMollification {n : ℕ} (E : Set (Euc n)) (k : Euc n → ℝ) : Euc n → ℝ :=
  E.indicator (fun _ ↦ (1:ℝ)) ⋆[lsmul ℝ ℝ, volume] k

theorem phaseMollification_contDiff {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {k : Euc n → ℝ} (hk : ContDiff ℝ ∞ k)
    (hc : HasCompactSupport k) : ContDiff ℝ ∞ (phaseMollification E k) :=
  hc.contDiff_convolution_right _ ((locallyIntegrable_const (1:ℝ)).indicator hE) hk

theorem phaseMollification_eq_setIntegral {n : ℕ} (E : Set (Euc n))
    (hE : MeasurableSet E) (k : Euc n → ℝ) (x : Euc n) :
    phaseMollification E k x = ∫ y in E, k (x-y) := by
  change (∫ y, E.indicator (fun _ ↦ (1:ℝ)) y*k (x-y)) = _
  have he : (fun y ↦ E.indicator (fun _ ↦ (1:ℝ)) y*k (x-y)) =
      E.indicator (fun y ↦ k (x-y)) := by
    funext y
    by_cases hy : y ∈ E <;> simp [hy]
  rw [he,integral_indicator hE]

theorem phaseMollification_mem_Icc {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {k : Euc n → ℝ} (hk : Integrable k volume)
    (hpos : ∀ x, 0 ≤ k x) (hunit : ∫ x, k x = 1) (x : Euc n) :
    phaseMollification E k x ∈ Icc (0:ℝ) 1 := by
  rw [phaseMollification_eq_setIntegral E hE]
  constructor
  · exact integral_nonneg fun y ↦ hpos _
  · calc
      _ ≤ ∫ y, k (x-y) := setIntegral_le_integral (hk.comp_sub_left x)
        (ae_of_all _ (fun y ↦ hpos _))
      _ = 1 := by rw [integral_sub_left_eq_self,hunit]

theorem negative_normal_flux_le_tilt {n : ℕ} (N : Euc n) {v : Euc n}
    (hv : ‖v‖ = 1) : 2*max (-inner ℝ N v) 0 ≤ ‖N-v‖^2 := by
  rw [norm_sub_sq_real,hv]
  rcases le_total (-inner ℝ N v) 0 with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg ‖N-v‖,norm_sub_sq_real N v]
  · rw [max_eq_left h]
    nlinarith [sq_nonneg ‖N‖]

theorem phaseMollification_fderiv {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {k : Euc n → ℝ} (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (x v : Euc n) {R : ℝ} (hR : 0 < R)
    (hs : tsupport (fun y ↦ k (x-y)) ⊆ Metric.ball 0 R) :
    fderiv ℝ (phaseMollification E k) x v =
      -(∫ y in Metric.ball 0 R, k (x-y)*inner ℝ (approximateNormal E y) v
        ∂perimeterMeasure E) := by
  let φ : Euc n → ℝ := fun y ↦ k (x-y)
  have hφ : ContDiff ℝ ∞ φ := hk.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport φ := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hd (y : Euc n) : fderiv ℝ φ y v = -fderiv ℝ k (x-y) v := by
    have h := ((hk.differentiable (by simp) (x-y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))).fderiv
    simpa only [φ,Function.comp_def,sub_apply,zero_apply,id_apply,
      zero_sub,ContinuousLinearMap.comp_apply,neg_apply,map_neg] using
      congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L v) h
  have hfi : LocallyIntegrable (E.indicator (fun _ ↦ (1:ℝ))) volume :=
    (locallyIntegrable_const (1:ℝ)).indicator hmin.1
  have hdiff : fderiv ℝ (phaseMollification E k) x v = -(∫ y in E, fderiv ℝ φ y v) := by
    rw [phaseMollification,(hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hfi
      (hk.of_le (by simp)) x).fderiv,
      convolution_precompR_apply (lsmul ℝ ℝ) hfi (hc.fderiv ℝ)
        (hk.continuous_fderiv (by simp))]
    change (∫ y, E.indicator (fun _ ↦ (1:ℝ)) y*fderiv ℝ k (x-y) v) = _
    simp_rw [hd,integral_neg,neg_neg]
    have he : (fun y ↦ E.indicator (fun _ ↦ (1:ℝ)) y*fderiv ℝ k (x-y) v) =
        E.indicator (fun y ↦ fderiv ℝ k (x-y) v) := by
      funext y
      by_cases hy : y ∈ E <;> simp [hy]
    rw [he,integral_indicator hmin.1]
  rw [hdiff,← divergence_scalar_direction (hφ.differentiable (by simp)) v,
    minimizing_gaussGreen_local hn hmin (Metric.ball 0 R) Metric.isOpen_ball
      (hmin.2.1 0 R hR).ne (fun y ↦ φ y • v) (hφ.smul contDiff_const)
      hcφ.smul_right (tsupport_smul_subset_left _ _ |>.trans hs)]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun y ↦ by simp only [φ,real_inner_smul_right]

theorem positive_neg_convolution_le {n : ℕ} (μ : Measure (Euc n))
    {f k : Euc n → ℝ} (hf : Integrable f μ) (hk : Continuous k)
    (hc : HasCompactSupport k) (hp : ∀ x, 0 ≤ k x) (x : Euc n) :
    max (-(f ⋆[lsmul ℝ ℝ, μ] k) x) 0 ≤
      ((fun y ↦ max (-f y) 0) ⋆[lsmul ℝ ℝ, μ] k) x := by
  have hq : Integrable (fun y ↦ max (-f y) 0) μ := hf.neg_part
  have hi := hc.convolutionExists_right (lsmul ℝ ℝ) hf.locallyIntegrable hk x
  have hj := hc.convolutionExists_right (lsmul ℝ ℝ) hq.locallyIntegrable hk x
  change max (-(∫ y, f y*k (x-y) ∂μ)) 0 ≤ ∫ y, max (-f y) 0*k (x-y) ∂μ
  apply max_le
  · rw [← integral_neg]
    apply integral_mono hi.neg hj
    intro y
    change -(f y*k (x-y)) ≤ max (-f y) 0*k (x-y)
    simpa only [neg_mul] using mul_le_mul_of_nonneg_right (le_max_left (-f y) 0) (hp _)
  · exact integral_nonneg fun y ↦ mul_nonneg (le_max_right _ _) (hp _)

theorem phaseMollification_positive_derivative_le_tilt {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E) {v : Euc n}
    (hv : ‖v‖ = 1) {k : Euc n → ℝ} (hk : ContDiff ℝ ∞ k)
    (hc : HasCompactSupport k) (hp : ∀ x, 0 ≤ k x) (hu : ∫ x, k x = 1)
    {R : ℝ} (hR : 0 < R) (c : Euc n) (r : ℝ)
    (hs : ∀ x ∈ Metric.closedBall c r, tsupport (fun y ↦ k (x-y)) ⊆ Metric.ball 0 R) :
    (∫ x in Metric.closedBall c r,
      max (fderiv ℝ (phaseMollification E k) x v) 0) ≤
      orientedTilt E v (Metric.ball 0 R) / 2 := by
  let μ := (perimeterMeasure E).restrict (Metric.ball 0 R)
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 0 R hR⟩
  let f : Euc n → ℝ := fun y ↦ inner ℝ (approximateNormal E y) v
  let q : Euc n → ℝ := fun y ↦ max (-f y) 0
  have hm : Measurable f := (measurable_approximateNormal hmin.1).inner measurable_const
  have hf : Integrable f μ := (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun y ↦ by
      change ‖inner ℝ (approximateNormal E y) v‖ ≤ 1
      exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (by
        rw [hv,mul_one]; exact approximateNormal_norm_le_one E y))
  have hq : Integrable q μ := hf.neg_part
  have hki : Integrable k volume := hk.continuous.integrable_of_hasCompactSupport hc
  have hconv : Integrable (q ⋆[lsmul ℝ ℝ, μ] k) volume :=
    (hq.convolution_integrand (lsmul ℝ ℝ) hki).integral_prod_left
  have hpos : ∀ x, 0 ≤ (q ⋆[lsmul ℝ ℝ, μ] k) x := by
    intro x
    exact integral_nonneg fun y ↦ mul_nonneg (le_max_right _ _) (hp _)
  have hdiff := (phaseMollification_contDiff hmin.1 hk hc).continuous_fderiv (by simp)
  have hleft : IntegrableOn (fun x ↦ max (fderiv ℝ (phaseMollification E k) x v) 0)
      (Metric.closedBall c r) volume :=
    ((hdiff.clm_apply continuous_const).max continuous_const).continuousOn.integrableOn_compact
      (isCompact_closedBall c r)
  have hpoint : ∀ x ∈ Metric.closedBall c r,
      max (fderiv ℝ (phaseMollification E k) x v) 0 ≤
        (q ⋆[lsmul ℝ ℝ, μ] k) x := by
    intro x hx
    rw [phaseMollification_fderiv hn hmin hk hc x v hR (hs x hx)]
    have h := positive_neg_convolution_le μ hf hk.continuous hc hp x
    convert h using 1
    congr 2
    apply integral_congr_ae
    exact ae_of_all _ fun y ↦ mul_comm _ _
  have htilt : Integrable (fun y ↦ ‖approximateNormal E y-v‖^2) μ := by
    apply (integrable_const (4:ℝ)).mono'
      (((measurable_approximateNormal hmin.1).sub measurable_const).norm.pow_const 2).aestronglyMeasurable
    apply ae_of_all μ
    intro y
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have hb : ‖approximateNormal E y-v‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by rw [hv]; linarith [approximateNormal_norm_le_one E y])
    change ‖approximateNormal E y-v‖^2 ≤ 4
    nlinarith [norm_nonneg (approximateNormal E y-v)]
  calc
    _ ≤ ∫ x in Metric.closedBall c r, (q ⋆[lsmul ℝ ℝ, μ] k) x :=
      setIntegral_mono_on hleft hconv.integrableOn measurableSet_closedBall hpoint
    _ ≤ ∫ x, (q ⋆[lsmul ℝ ℝ, μ] k) x :=
      setIntegral_le_integral hconv (ae_of_all _ hpos)
    _ = ∫ y, q y ∂μ := by rw [integral_convolution (lsmul ℝ ℝ) hq hki,hu]; simp
    _ ≤ _ := by
      dsimp [orientedTilt]
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      rw [← integral_mul_const]
      apply integral_mono (hq.mul_const 2) htilt
      intro y
      simpa only [q,f,mul_comm] using negative_normal_flux_le_tilt (approximateNormal E y) hv

end RPISingularHarnack

end

end OAI
