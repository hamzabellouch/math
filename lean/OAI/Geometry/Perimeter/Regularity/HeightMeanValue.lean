import OAI.Geometry.Perimeter.Regularity.SmulMemPhaseSupport

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Pointwise
namespace RPISingularHarnack
open RPI.Boundary

private theorem gradient_affine_height {n : ℕ} (v : Euc n) (a : ℝ) (x : Euc n) :
    gradient (fun y ↦ inner ℝ v y - a) x = v := by
  apply HasGradientAt.gradient
  change HasFDerivAt (fun y ↦ inner ℝ v y - a)
    ((InnerProductSpace.toDual ℝ (Euc n)) v) x
  exact (innerSL ℝ v).hasFDerivAt.sub_const a

private theorem gradient_radial_primitive {n : ℕ} (c : Euc n) (t : ℝ)
    {Ψ ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hdΨ : ∀ s, deriv Ψ s = ψ s)
    (x : Euc n) :
    gradient (fun y ↦ Ψ (t^2 * ‖y-c‖^2)) x =
      (2*t^2*ψ (t^2*‖x-c‖^2)) • (x-c) := by
  have hi := (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c).norm_sq).const_mul (t^2)
  have hh := ((hΨ.differentiable (by simp)) _).hasDerivAt.comp_hasFDerivAt x hi
  rw [hdΨ] at hh
  change HasFDerivAt (fun y : Euc n ↦ Ψ (t^2 * ‖y-c‖^2)) _ x at hh
  apply (InnerProductSpace.toDual ℝ (Euc n)).injective
  rw [toDual_gradient, hh.fderiv]
  ext z
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, id_eq, innerSL_apply_apply, map_smul,
    InnerProductSpace.toDual_apply_apply, smul_eq_mul]
  ring

theorem minimizing_height_radialDerivative_nonpos {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c v : Euc n) (a : ℝ) {M : ℝ} (hM : 0 < M)
    {Ψ ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hψ : ContDiff ℝ ∞ ψ)
    (hdΨ : ∀ s, deriv Ψ s = ψ s)
    (hΨz : ∀ s, 1 ≤ s → Ψ s = 0) (hψz : ∀ s, 1 ≤ s → ψ s = 0)
    (hΨ0 : ∀ s, Ψ s ≤ 0) (hψd : ∀ s, deriv ψ s ≤ 0)
    {t : ℝ} (ht : 1/M < t) :
    (∫ x in Metric.ball c M, (inner ℝ v x-a)^2 *
      radialDensityDerivative c (n-1) ψ t x ∂perimeterMeasure E) ≤ 0 := by
  let μ := (perimeterMeasure E).restrict (Metric.ball c M)
  have := perimeterMeasure_locallyFinite E hmin.2.1
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 c M hM⟩
  have ht0 : 0 < t := (one_div_pos.mpr hM).trans ht
  have htM : 1/t < M := (div_lt_iff₀ ht0).mpr (by
    have := (div_lt_iff₀ hM).mp ht
    nlinarith)
  let H : Euc n → ℝ := fun x ↦ inner ℝ v x-a
  let P : Euc n → ℝ := fun x ↦ Ψ (t^2*‖x-c‖^2)
  let Q : Euc n → ℝ := fun x ↦ ψ (t^2*‖x-c‖^2)
  let V : Euc n → Euc n := fun x ↦ Q x • (x-c)
  let W : Euc n → Euc n := fun x ↦ H x^2 • V x
  let φ : Euc n → ℝ := fun x ↦ H x * P x
  have hH : ContDiff ℝ ∞ H := (contDiff_const.inner ℝ contDiff_id).sub contDiff_const
  have hP : ContDiff ℝ ∞ P :=
    hΨ.comp (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ)))
  have hQ : ContDiff ℝ ∞ Q :=
    hψ.comp (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ)))
  have hV : ContDiff ℝ ∞ V := hQ.smul (𝕜' := ℝ) (contDiff_id.sub contDiff_const)
  have hW : ContDiff ℝ ∞ W := (hH.pow 2).smul (𝕜' := ℝ) hV
  have hφ : ContDiff ℝ ∞ φ := hH.mul hP
  have hsV : tsupport V ⊆ Metric.closedBall c (1/t) :=
    (tsupport_smul_subset_left _ _).trans (radialProfile_tsupport c hψz ht0)
  have hsW : tsupport W ⊆ Metric.closedBall c (1/t) :=
    (tsupport_smul_subset_right (fun x ↦ H x^2) V).trans hsV
  have hsφ : tsupport φ ⊆ Metric.closedBall c (1/t) :=
    tsupport_mul_subset_right.trans (radialProfile_tsupport c hΨz ht0)
  have hcW : HasCompactSupport W :=
    (isCompact_closedBall c (1/t)).of_isClosed_subset (isClosed_tsupport _) hsW
  have hcφ : HasCompactSupport φ :=
    (isCompact_closedBall c (1/t)).of_isClosed_subset (isClosed_tsupport _) hsφ
  have hzW := minimizing_tangentialDivergence_integral_eq_zero hn hmin c hM hW hcW
    (hsW.trans (Metric.closedBall_subset_ball htM))
  have hzφ := minimizing_tangentialGradient_integral_eq_zero_local hn hmin c hM hφ hcφ
    (hsφ.trans (Metric.closedBall_subset_ball htM)) v
  have hiD : Integrable (fun x ↦ H x^2 * radialDensityDerivative c (n-1) ψ t x) μ := by
    exact (((hH.continuous.pow 2).mul
      ((radialDensityDerivative_continuous c (n-1) hψ).comp
        (continuous_const.prodMk continuous_id))).continuousOn.integrableOn_compact
        (isCompact_closedBall c M)).mono_set Metric.ball_subset_closedBall
  have hiW := (tangentialDivergence_integrable_ball_perimeter hmin c hM hW).const_mul
    (t^((n-1)-1))
  have hiφ := ((tangentialGradient_integrable_ball_perimeter hmin c hM
    (hφ.of_le (by simp))).inner_const v).const_mul (t^((n-1)-1)/t^2)
  have hcmp : ∀ᵐ x ∂μ,
      H x^2 * radialDensityDerivative c (n-1) ψ t x ≤
        t^((n-1)-1) * tangentialDivergence E W x -
          (t^((n-1)-1)/t^2) * inner ℝ (tangentialGradient E φ x) v := by
    filter_upwards [ae_restrict_of_ae (minimizing_halfspaceBlowup_ae hn hmin)] with x hx
    have hpow : t^(n-1) = t^((n-1)-1)*t := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n-1)]
    have hgH := gradient_affine_height v a x
    change gradient H x = v at hgH
    have hGnonneg : 0 ≤ ‖v‖^2 - (inner ℝ v (approximateNormal E x))^2 := by
      have hh := norm_inner_le_norm (𝕜 := ℝ) v (approximateNormal E x)
      rw [hx.1, mul_one, Real.norm_eq_abs] at hh
      have hsq := mul_self_le_mul_self (abs_nonneg _) hh
      nlinarith [sq_abs (inner ℝ v (approximateNormal E x))]
    have hf : inner ℝ (tangentialGradient E φ x) v =
        P x * (‖v‖^2 - (inner ℝ v (approximateNormal E x))^2) +
        (2*t^2*H x*Q x) * (inner ℝ v (x-c) -
          inner ℝ v (approximateNormal E x) * inner ℝ (approximateNormal E x) (x-c)) := by
      dsimp only [φ]
      rw [tangentialGradient_mul E (hH.differentiable (by simp) x)
        (hP.differentiable (by simp) x)]
      simp only [inner_add_left, real_inner_smul_left, tangentialGradient, hgH]
      rw [show gradient P x = (2*t^2*Q x) • (x-c) from
        gradient_radial_primitive c t hΨ hdΨ x]
      simp only [inner_sub_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      simp only [inner_sub_right]
      simp only [real_inner_comm]
      ring
    have hgh2 : tangentialGradient E (fun y ↦ H y^2) x =
        (2*H x) • tangentialGradient E H x := by
      have he : (fun y ↦ H y^2) = fun y ↦ H y*H y := by funext y; ring
      rw [he, tangentialGradient_mul E (hH.differentiable (by simp) x)
        (hH.differentiable (by simp) x)]
      module
    have hdiv : tangentialDivergence E W x =
        H x^2 * ((n-1:ℕ)* Q x + 2*t^2*deriv ψ (t^2*‖x-c‖^2) *
          (‖x-c‖^2 - (inner ℝ (approximateNormal E x) (x-c))^2)) +
        (2*H x*Q x) * (inner ℝ v (x-c) -
          inner ℝ v (approximateNormal E x) * inner ℝ (approximateNormal E x) (x-c)) := by
      dsimp only [W]
      rw [tangentialDivergence_smul E ((hH.pow 2).differentiable (by simp))
        (hV.differentiable (by simp)), hgh2]
      rw [show tangentialDivergence E V x = _ from
        tangentialDivergence_radialProfile (by omega) E c hψ t x hx.1]
      simp only [V, tangentialGradient, hgH, inner_sub_left, real_inner_smul_left,
        real_inner_smul_right]
      ring
    rw [hf, hdiv]
    have hbad : (t^((n-1)-1)/t^2) * P x *
        (‖v‖^2 - (inner ℝ v (approximateNormal E x))^2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (hΨ0 _)) hGnonneg
    have hrad : 2*t^((n-1)-1)*t^2 * H x^2 *
        (inner ℝ (approximateNormal E x) (x-c))^2 * deriv ψ (t^2*‖x-c‖^2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (hψd _)
    have halg : H x^2 * radialDensityDerivative c (n-1) ψ t x =
        t^((n-1)-1) *
          (H x^2 * ((n-1:ℕ)*Q x + 2*t^2*deriv ψ (t^2*‖x-c‖^2) *
            (‖x-c‖^2-(inner ℝ (approximateNormal E x) (x-c))^2)) +
            (2*H x*Q x)*(inner ℝ v (x-c)-inner ℝ v (approximateNormal E x)*
              inner ℝ (approximateNormal E x) (x-c))) -
          (t^((n-1)-1)/t^2) * (P x*(‖v‖^2-(inner ℝ v (approximateNormal E x))^2)+
            (2*t^2*H x*Q x)*(inner ℝ v (x-c)-inner ℝ v (approximateNormal E x)*
              inner ℝ (approximateNormal E x) (x-c))) +
          (t^((n-1)-1)/t^2) * P x*(‖v‖^2-(inner ℝ v (approximateNormal E x))^2) +
          2*t^((n-1)-1)*t^2*H x^2*(inner ℝ (approximateNormal E x) (x-c))^2*
            deriv ψ (t^2*‖x-c‖^2) := by
      dsimp only [radialDensityDerivative, Q]
      rw [hpow]
      field_simp
      ring
    linarith
  have hh := integral_mono_ae hiD (hiW.sub hiφ) hcmp
  simp only [Pi.sub_apply] at hh
  dsimp only [μ] at hh
  rw [integral_sub hiW hiφ, integral_const_mul, integral_const_mul] at hh
  change _ ≤ _ * (∫ x in Metric.ball c M, tangentialDivergence E W x ∂perimeterMeasure E) -
    _ * (∫ x in Metric.ball c M, inner ℝ (tangentialGradient E φ x) v ∂perimeterMeasure E) at hh
  simpa only [hzW, hzφ, mul_zero, sub_self] using hh

def densityPrimitive (j : ℕ) (s : ℝ) : ℝ :=
  ∫ z in (1:ℝ)..s, densityProfile j z

theorem densityPrimitive_hasDerivAt (j : ℕ) (s : ℝ) :
    HasDerivAt (densityPrimitive j) (densityProfile j s) s := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((densityProfile_contDiff j).continuous.intervalIntegrable 1 s)
    (densityProfile_contDiff j).continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    (densityProfile_contDiff j).continuous.continuousAt

theorem densityPrimitive_deriv (j : ℕ) (s : ℝ) :
    deriv (densityPrimitive j) s = densityProfile j s := (densityPrimitive_hasDerivAt j s).deriv

theorem densityPrimitive_contDiff (j : ℕ) : ContDiff ℝ ∞ (densityPrimitive j) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun s ↦ (densityPrimitive_hasDerivAt j s).differentiableAt, ?_⟩
  simpa only [funext (densityPrimitive_deriv j)] using densityProfile_contDiff j

theorem densityPrimitive_zero (j : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    densityPrimitive j s = 0 := by
  unfold densityPrimitive
  trans ∫ z in (1:ℝ)..s, (0:ℝ)
  · apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le hs] at hz
    exact densityProfile_zero j hz.1
  · simp

theorem densityPrimitive_nonpos (j : ℕ) (s : ℝ) : densityPrimitive j s ≤ 0 := by
  by_cases hs : 1 ≤ s
  · rw [densityPrimitive_zero j hs]
  · unfold densityPrimitive
    rw [intervalIntegral.integral_symm]
    exact neg_nonpos.mpr (intervalIntegral.integral_nonneg (le_of_not_ge hs)
      fun z _ ↦ (densityProfile_mem_Icc j z).1)

private theorem integral_hasDerivAt_compact_window {n : ℕ}
    {F D : ℝ → Euc n → ℝ} (hF : Continuous (Function.uncurry F))
    (hD : Continuous (Function.uncurry D))
    (hd : ∀ s x, HasDerivAt (fun t ↦ F t x) (D s x) s)
    (μ : Measure (Euc n)) [IsFiniteMeasure μ]
    {K : Set (Euc n)} (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K) (t : ℝ) :
    HasDerivAt (fun s ↦ ∫ x, F s x ∂μ) (∫ x, D t x ∂μ) t := by
  have hFt : Continuous (F t) := hF.comp (continuous_const.prodMk continuous_id)
  have hDt : Continuous (D t) := hD.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hFt.continuousOn
  have hFi : Integrable (F t) μ :=
    Integrable.of_bound hFt.aestronglyMeasurable C (hμ.mono fun x hx ↦ hC x hx)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hD.continuousOn : ContinuousOn _ (Icc (t-1) (t+1) ×ˢ K))
  have hbound : ∀ᵐ x ∂μ, ∀ s ∈ Ioo (t-1) (t+1), ‖D s x‖ ≤ B := by
    filter_upwards [hμ] with x hx
    intro s hs
    exact hB (s,x) ⟨⟨hs.1.le, hs.2.le⟩,hx⟩
  have hderiv : ∀ᵐ x ∂μ, ∀ s ∈ Ioo (t-1) (t+1),
      HasDerivAt (fun t ↦ F t x) (D s x) s := ae_of_all μ fun x s _ ↦ hd s x
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (s := Ioo (t-1) (t+1)) (bound := fun _ ↦ B)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s ↦ (hF.comp ((continuous_const : Continuous (fun _ : Euc n ↦ s)).prodMk continuous_id)).aestronglyMeasurable)
    hFi hDt.aestronglyMeasurable hbound (integrable_const B) hderiv).2

theorem height_radial_integral_hasDerivAt {n : ℕ}
    (c v : Euc n) (a M : ℝ) (k : ℕ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (μ : Measure (Euc n)) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Metric.closedBall c M) (t : ℝ) :
    HasDerivAt (fun s ↦ ∫ x, (inner ℝ v x-a)^2 * radialDensityIntegrand c k ψ s x ∂μ)
      (∫ x, (inner ℝ v x-a)^2 * radialDensityDerivative c k ψ t x ∂μ) t := by
  let H : Euc n → ℝ := fun x ↦ (inner ℝ v x-a)^2
  have hH : Continuous H := ((continuous_const.inner continuous_id).sub continuous_const).pow 2
  have hcF : Continuous (fun p : ℝ × Euc n ↦ H p.2 * radialDensityIntegrand c k ψ p.1 p.2) :=
    (hH.comp continuous_snd).mul (radialDensityIntegrand_continuous c k hψ)
  have hcD : Continuous (fun p : ℝ × Euc n ↦ H p.2 * radialDensityDerivative c k ψ p.1 p.2) :=
    (hH.comp continuous_snd).mul (radialDensityDerivative_continuous c k hψ)
  exact integral_hasDerivAt_compact_window hcF hcD
    (fun s x ↦ (radialDensityIntegrand_hasDerivAt c k hψ s x).const_mul (H x))
    μ (isCompact_closedBall c M) hμ t

theorem minimizing_height_smoothedDensity_antitoneOn {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c v : Euc n) (a : ℝ) {M : ℝ} (hM : 0 < M) (j : ℕ) :
    AntitoneOn (fun t ↦ ∫ x in Metric.ball c M, (inner ℝ v x-a)^2 *
      radialDensityIntegrand c (n-1) (densityProfile j) t x ∂perimeterMeasure E) (Ioi (1/M)) := by
  let μ := (perimeterMeasure E).restrict (Metric.ball c M)
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 c M hM⟩
  have hμ : ∀ᵐ x ∂μ, x ∈ Metric.closedBall c M :=
    (ae_restrict_mem measurableSet_ball).mono fun _ hx ↦ Metric.ball_subset_closedBall hx
  have hd := fun t ↦ height_radial_integral_hasDerivAt c v a M (n-1)
    (densityProfile_contDiff j) μ hμ t
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi (1/M))
    (fun t _ ↦ (hd t).continuousAt.continuousWithinAt)
    (fun t _ ↦ (hd t).hasDerivWithinAt)
  intro t ht
  exact minimizing_height_radialDerivative_nonpos hn hmin c v a hM
    (densityPrimitive_contDiff j) (densityProfile_contDiff j) (densityPrimitive_deriv j)
    (fun s hs ↦ densityPrimitive_zero j hs) (fun s hs ↦ densityProfile_zero j hs)
    (densityPrimitive_nonpos j) (densityProfile_deriv_nonpos j)
    (by simpa only [interior_Ioi, mem_Ioi] using ht)

theorem height_radial_integral_tendsto {n : ℕ}
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c v : Euc n) (a : ℝ) {M : ℝ} (hM : 0 < M) {t : ℝ} (ht : 1/M < t) :
    Tendsto (fun j ↦ ∫ x in Metric.ball c M, (inner ℝ v x-a)^2 *
      radialDensityIntegrand c (n-1) (densityProfile j) t x ∂perimeterMeasure E) atTop
      (𝓝 (t^(n-1) * ∫ x in Metric.ball c (1/t), (inner ℝ v x-a)^2 ∂perimeterMeasure E)) := by
  let μ := (perimeterMeasure E).restrict (Metric.ball c M)
  let H : Euc n → ℝ := fun x ↦ (inner ℝ v x-a)^2
  have hH : Continuous H := ((continuous_const.inner continuous_id).sub continuous_const).pow 2
  have := perimeterMeasure_locallyFinite E hmin.2.1
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 c M hM⟩
  have ht0 : 0 < t := (one_div_pos.mpr hM).trans ht
  have htM : 1/t < M := (div_lt_iff₀ ht0).mpr (by
    have := (div_lt_iff₀ hM).mp ht
    nlinarith)
  have hiH : Integrable H μ := (hH.continuousOn.integrableOn_compact
    (isCompact_closedBall c M)).mono_set Metric.ball_subset_closedBall
  have hh := tendsto_integral_of_dominated_convergence (μ := μ) (fun x ↦ H x*t^(n-1))
    (fun j ↦ (hH.mul (((radialDensityIntegrand_continuous c (n-1) (densityProfile_contDiff j)).comp
      (continuous_const.prodMk continuous_id)))).aestronglyMeasurable)
    (hiH.mul_const _) (fun j ↦ ae_of_all μ fun x ↦ ?_)
    (ae_of_all μ fun x ↦ (tendsto_const_nhds (x := H x)).mul
      (radialDensityIntegrand_tendsto c (n-1) ht0 x))
  · have heq : (∫ x, H x * (Metric.ball c (1/t)).indicator (fun _ ↦ t^(n-1)) x ∂μ) =
        t^(n-1) * ∫ x in Metric.ball c (1/t), H x ∂perimeterMeasure E := by
      have hpt : ∀ x, H x * (Metric.ball c (1/t)).indicator (fun _ ↦ t^(n-1)) x =
          t^(n-1) * (Metric.ball c (1/t)).indicator H x := by
        intro x
        by_cases hx : x ∈ Metric.ball c (1/t)
        · rw [indicator_of_mem hx, indicator_of_mem hx, mul_comm]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero, mul_zero]
      simp_rw [hpt]
      rw [integral_const_mul, integral_indicator measurableSet_ball]
      dsimp only [μ]
      rw [Measure.restrict_restrict measurableSet_ball,
        inter_eq_left.mpr (Metric.ball_subset_ball htM.le)]
    rwa [heq] at hh
  · change |(inner ℝ v x-a)^2 * (t^(n-1)*densityProfile j (t^2*‖x-c‖^2))| ≤
      (inner ℝ v x-a)^2 * t^(n-1)
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg
      (pow_nonneg ht0.le _) (densityProfile_mem_Icc j _).1))]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (pow_nonneg ht0.le _) (densityProfile_mem_Icc j _).2) (sq_nonneg _)

theorem minimizing_height_density_monotone {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E) (c v : Euc n) (a : ℝ) :
    MonotoneOn (fun r : ℝ ↦ (∫ x in Metric.ball c r,
      (inner ℝ v x-a)^2 ∂perimeterMeasure E) / r^(n-1)) (Ioi 0) := by
  intro r hr R hR hrR
  have hr0 : 0 < r := hr
  have hR0 : 0 < R := hR
  let M := 2*R
  have hM : 0 < M := by dsimp [M]; positivity
  have hRM : 1/M < 1/R := one_div_lt_one_div_of_lt hR0 (by dsimp [M]; linarith)
  have htr : 1/R ≤ 1/r := one_div_le_one_div_of_le hr0 hrR
  have hrM : 1/M < 1/r := hRM.trans_le htr
  have hseq (j : ℕ) := minimizing_height_smoothedDensity_antitoneOn hn hmin c v a hM j hRM hrM htr
  have hh := le_of_tendsto_of_tendsto
    (height_radial_integral_tendsto hmin c v a hM hrM)
    (height_radial_integral_tendsto hmin c v a hM hRM) (Eventually.of_forall hseq)
  simpa [one_div, div_eq_mul_inv, mul_comm] using hh

theorem exists_minimizing_height_mean_value_constant (n : ℕ) (hn : 1 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ E : Set (Euc n), IsLocallyPerimeterMinimizing E →
      ∀ p ∈ perimeterSupport E, ∀ R : ℝ, 0 < R → ∀ (v : Euc n) (a : ℝ),
        (inner ℝ v p-a)^2 ≤ C/R^(n-1) *
          ∫ x in Metric.ball p R, (inner ℝ v x-a)^2 ∂perimeterMeasure E := by
  obtain ⟨c₀, hc₀, hdensity⟩ := exists_minimizing_perimeter_lower_density n hn
  refine ⟨2/c₀, by positivity, ?_⟩
  intro E hmin p hp R hR v a
  let H : Euc n → ℝ := fun x ↦ (inner ℝ v x-a)^2
  have hH : Continuous H := ((continuous_const.inner continuous_id).sub continuous_const).pow 2
  have hI0 : 0 ≤ ∫ x in Metric.ball p R, H x ∂perimeterMeasure E :=
    integral_nonneg fun x ↦ sq_nonneg _
  by_cases hz : H p = 0
  · change H p ≤ _
    rw [hz]
    exact mul_nonneg (by positivity) hI0
  have hp0 : 0 < H p := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
  have ht : {x | H p/2 < H x} ∈ 𝓝 p :=
    hH.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by linarith))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp ht
  let ρ := min r R
  have hρ : 0 < ρ := lt_min hr hR
  have hρr : ρ ≤ r := min_le_left _ _
  have hρR : ρ ≤ R := min_le_right _ _
  have := perimeterMeasure_locallyFinite E hmin.2.1
  have : IsFiniteMeasure ((perimeterMeasure E).restrict (Metric.ball p ρ)) := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 p ρ hρ⟩
  have hiH : IntegrableOn H (Metric.ball p ρ) (perimeterMeasure E) :=
    (hH.continuousOn.integrableOn_compact (isCompact_closedBall p ρ)).mono_set
      Metric.ball_subset_closedBall
  have hlow : (H p/2) * (perimeterMeasure E).real (Metric.ball p ρ) ≤
      ∫ x in Metric.ball p ρ, H x ∂perimeterMeasure E := by
    have hh := integral_mono_ae (integrable_const (H p/2)) hiH
      ((ae_restrict_mem measurableSet_ball).mono fun x hx ↦
        (hsub (Metric.ball_subset_ball hρr hx)).le)
    simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ,
      mul_comm] using hh
  have hd : c₀*ρ^(n-1) ≤ (perimeterMeasure E).real (Metric.ball p ρ) := by
    have hd₀ := ENNReal.toReal_mono (hmin.2.1 p ρ hρ).ne (hdensity E hmin p hp ρ hρ)
    rw [ENNReal.toReal_ofReal (by positivity)] at hd₀
    simpa only [Measure.real, perimeterMeasure_open E Metric.isOpen_ball] using hd₀
  have hmono := minimizing_height_density_monotone hn hmin p v a hρ hR hρR
  have hbound : c₀*H p/2 ≤ (∫ x in Metric.ball p R, H x ∂perimeterMeasure E)/R^(n-1) := by
    calc
      _ = ((H p/2)*(c₀*ρ^(n-1)))/ρ^(n-1) := by
        field_simp
      _ ≤ ((H p/2)*(perimeterMeasure E).real (Metric.ball p ρ))/ρ^(n-1) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hd (by positivity)) (pow_nonneg hρ.le _)
      _ ≤ (∫ x in Metric.ball p ρ, H x ∂perimeterMeasure E)/ρ^(n-1) :=
        div_le_div_of_nonneg_right hlow (pow_nonneg hρ.le _)
      _ ≤ _ := hmono
  change H p ≤ (2/c₀)/R^(n-1) * ∫ x in Metric.ball p R, H x ∂perimeterMeasure E
  calc
    H p = (2/c₀)*(c₀*H p/2) := by field_simp
    _ ≤ (2/c₀)*((∫ x in Metric.ball p R, H x ∂perimeterMeasure E)/R^(n-1)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

end RPISingularHarnack

end

end OAI
