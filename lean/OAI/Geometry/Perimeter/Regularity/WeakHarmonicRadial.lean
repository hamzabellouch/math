import OAI.Geometry.Perimeter.Regularity.HeightMeanValue

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

def WeakHarmonicOn (u : Euc n → ℝ) (U : Set (Euc n)) : Prop :=
  ∀ φ : Euc n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∫ x, u x * divergence (gradient φ) x) = 0

theorem divergence_displacement (c x : Euc n) :
    divergence (fun y ↦ y-c) x = n := by
  have hd : fderiv ℝ (fun y : Euc n ↦ y-c) x = ContinuousLinearMap.id ℝ (Euc n) :=
    ((hasFDerivAt_id x).sub_const c).fderiv
  simp [divergence,hd]

theorem gradient_radialPrimitive (c : Euc n) (t : ℝ)
    {Ψ ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hdΨ : ∀ s, deriv Ψ s = ψ s)
    (x : Euc n) :
    gradient (fun y ↦ Ψ (t^2*‖y-c‖^2)) x =
      (2*t^2*ψ (t^2*‖x-c‖^2)) • (x-c) := by
  have hi := (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c).norm_sq).const_mul (t^2)
  have hh := ((hΨ.differentiable (by simp)) _).hasDerivAt.comp_hasFDerivAt x hi
  rw [hdΨ] at hh
  change HasFDerivAt (fun y : Euc n ↦ Ψ (t^2*‖y-c‖^2)) _ x at hh
  apply (InnerProductSpace.toDual ℝ (Euc n)).injective
  rw [toDual_gradient,hh.fderiv]
  ext z
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,id_eq,innerSL_apply_apply,map_smul,
    InnerProductSpace.toDual_apply_apply,smul_eq_mul]
  ring

theorem laplacian_radialPrimitive (c : Euc n) (t : ℝ)
    {Ψ ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hψ : ContDiff ℝ ∞ ψ)
    (hdΨ : ∀ s, deriv Ψ s = ψ s) (x : Euc n) :
    divergence (gradient (fun y ↦ Ψ (t^2*‖y-c‖^2))) x =
      2*t^2*((n:ℝ)*ψ (t^2*‖x-c‖^2)+
        2*t^2*‖x-c‖^2*deriv ψ (t^2*‖x-c‖^2)) := by
  rw [funext (gradient_radialPrimitive c t hΨ hdΨ)]
  have hq : ContDiff ℝ ∞ (fun y : Euc n ↦ 2*t^2*ψ (t^2*‖y-c‖^2)) :=
    contDiff_const.mul (hψ.comp (contDiff_const.mul
      ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ))))
  have hV : Differentiable ℝ (fun y : Euc n ↦ y-c) := differentiable_id.sub_const c
  rw [divergence_smul (hq.differentiable (by simp)) hV,divergence_displacement,inner_gradient_left]
  have hi := (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c).norm_sq).const_mul (t^2)
  have hh := (((hψ.differentiable (by simp)) _).hasDerivAt.comp_hasFDerivAt x hi).const_mul (2*t^2)
  change HasFDerivAt (fun y : Euc n ↦ 2*t^2*ψ (t^2*‖y-c‖^2)) _ x at hh
  rw [hh.fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,id_eq,innerSL_apply_apply,smul_eq_mul,
    real_inner_self_eq_norm_sq]
  ring

theorem radial_average_hasDerivAt (c : Euc n) (R : ℝ) (k : ℕ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {u : Euc n → ℝ}
    (hu : IntegrableOn u (Metric.ball c R) volume) (t : ℝ) :
    IntegrableOn (fun x ↦ u x*radialDensityDerivative c k ψ t x) (Metric.ball c R) ∧
    HasDerivAt (fun s ↦ ∫ x in Metric.ball c R, u x*radialDensityIntegrand c k ψ s x)
      (∫ x in Metric.ball c R, u x*radialDensityDerivative c k ψ t x) t := by
  let μ := volume.restrict (Metric.ball c R)
  have hcF (s : ℝ) : Continuous (radialDensityIntegrand c k ψ s) :=
    (radialDensityIntegrand_continuous c k hψ).comp (continuous_const.prodMk continuous_id)
  have hcD (s : ℝ) : Continuous (radialDensityDerivative c k ψ s) :=
    (radialDensityDerivative_continuous c k hψ).comp (continuous_const.prodMk continuous_id)
  obtain ⟨C,hC⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn (hcF t).continuousOn
  have hFi : Integrable (fun x ↦ u x*radialDensityIntegrand c k ψ t x) μ := by
    apply hu.mul_bdd (hcF t).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hC x (Metric.ball_subset_closedBall hx)
  obtain ⟨B,hB⟩ := (isCompact_Icc.prod (isCompact_closedBall c R)).exists_bound_of_continuousOn
    ((radialDensityDerivative_continuous c k hψ).continuousOn :
      ContinuousOn _ (Icc (t-1) (t+1) ×ˢ Metric.closedBall c R))
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo (t-1) (t+1)) (bound := fun x ↦ ‖u x‖*B)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s ↦ hu.aestronglyMeasurable.mul (hcF s).aestronglyMeasurable)
    hFi (hu.aestronglyMeasurable.mul (hcD t).aestronglyMeasurable)
    ?_ (hu.norm.mul_const B) (Eventually.of_forall ?_)
  · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    intro s hs
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB (s,x) ⟨⟨hs.1.le,hs.2.le⟩,
      Metric.ball_subset_closedBall hx⟩) (norm_nonneg _)
  · intro x s _
    exact (radialDensityIntegrand_hasDerivAt c k hψ s x).const_mul (u x)

theorem tsupport_gradient_subset (φ : Euc n → ℝ) : tsupport (gradient φ) ⊆ tsupport φ := by
  exact (tsupport_comp_subset (map_zero (InnerProductSpace.toDual ℝ (Euc n)).symm) (fderiv ℝ φ)).trans
    (tsupport_fderiv_subset ℝ)

theorem weakHarmonic_radial_derivative_zero {u : Euc n → ℝ} {U : Set (Euc n)}
    (hw : WeakHarmonicOn u U) (hn : 0 < n) (c : Euc n) {R : ℝ} (hR : 0 < R)
    (hU : Metric.ball c R ⊆ U)
    {Ψ ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hψ : ContDiff ℝ ∞ ψ)
    (hdΨ : ∀ s, deriv Ψ s = ψ s) (hΨz : ∀ s, 1 ≤ s → Ψ s = 0)
    {t : ℝ} (ht : 1/R < t) :
    (∫ x in Metric.ball c R, u x*radialDensityDerivative c n ψ t x) = 0 := by
  have ht0 : 0 < t := (one_div_pos.mpr hR).trans ht
  have htR : 1/t < R := (div_lt_iff₀ ht0).mpr (by
    have := (div_lt_iff₀ hR).mp ht
    nlinarith)
  let φ : Euc n → ℝ := fun x ↦ Ψ (t^2*‖x-c‖^2)
  have hφ : ContDiff ℝ ∞ φ :=
    hΨ.comp (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ)))
  have hsφ : tsupport φ ⊆ Metric.ball c R :=
    (radialProfile_tsupport c hΨz ht0).trans (Metric.closedBall_subset_ball htR)
  have hcφ : HasCompactSupport φ := (isCompact_closedBall c R).of_isClosed_subset
    (isClosed_tsupport φ) (hsφ.trans Metric.ball_subset_closedBall)
  have hz := hw φ hφ hcφ (hsφ.trans hU)
  have hsL : Function.support (fun x ↦ u x*divergence (gradient φ) x) ⊆ Metric.ball c R :=
    (Function.support_mul_subset_right _ _).trans ((subset_tsupport _).trans
      ((tsupport_divergence_subset _).trans ((tsupport_gradient_subset φ).trans hsφ)))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦
    Function.notMem_support.mp (fun hh ↦ hx (hsL hh)))] at hz
  have hp : t^n = t^(n-1)*t := by rw [← pow_succ]; congr 1; omega
  have hid (x : Euc n) : u x*radialDensityDerivative c n ψ t x =
      (t^(n-1)/(2*t^2))*(u x*divergence (gradient φ) x) := by
    dsimp only [φ]
    rw [laplacian_radialPrimitive c t hΨ hψ hdΨ]
    dsimp only [radialDensityDerivative]
    rw [hp]
    field_simp [ht0.ne']
  simp_rw [hid]
  rw [integral_const_mul,hz,mul_zero]

theorem weakHarmonic_radial_average_eq {u : Euc n → ℝ} {U : Set (Euc n)}
    (hw : WeakHarmonicOn u U) (hn : 0 < n) (c : Euc n) {R : ℝ} (hR : 0 < R)
    (hu : IntegrableOn u (Metric.ball c R) volume) (hU : Metric.ball c R ⊆ U)
    (j : ℕ) {s t : ℝ} (hs : 1/R < s) (ht : 1/R < t) :
    (∫ x in Metric.ball c R, u x*radialDensityIntegrand c n (densityProfile j) s x) =
      ∫ x in Metric.ball c R, u x*radialDensityIntegrand c n (densityProfile j) t x := by
  apply isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (1/R)).isPreconnected
    (f := fun r ↦ ∫ x in Metric.ball c R, u x*radialDensityIntegrand c n (densityProfile j) r x)
  · intro r hr
    exact (radial_average_hasDerivAt c R n (densityProfile_contDiff j) hu r).2.differentiableAt.differentiableWithinAt
  · intro r hr
    rw [(radial_average_hasDerivAt c R n (densityProfile_contDiff j) hu r).2.deriv]
    exact weakHarmonic_radial_derivative_zero hw hn c hR hU
      (densityPrimitive_contDiff j) (densityProfile_contDiff j) (densityPrimitive_deriv j)
      (fun z hz ↦ densityPrimitive_zero j hz) hr
  · exact hs
  · exact ht

end RPISingularHarnack

end

end OAI
