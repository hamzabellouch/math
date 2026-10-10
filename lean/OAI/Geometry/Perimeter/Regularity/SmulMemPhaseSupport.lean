import OAI.Geometry.Perimeter.Regularity.ExistsTangentialGradientBallBound

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPISingularHarnack
open scoped Pointwise

theorem IsCone.smul_mem_phaseSupport {n : ℕ} {E : Set (Euc n)} (hcone : IsCone E)
    {x : Euc n} (hx : x ∈ (volume.restrict E).support) {r : ℝ} (hr : 0 < r) :
    r • x ∈ (volume.restrict E).support := by
  apply Metric.nhds_basis_ball.mem_measureSupport.mpr
  intro R hR
  rw [Measure.restrict_apply measurableSet_ball]
  have hp := Metric.nhds_basis_ball.mem_measureSupport.mp hx (R/r) (div_pos hR hr)
  rw [Measure.restrict_apply measurableSet_ball] at hp
  have hs : r • (Metric.ball x (R/r) ∩ E) ⊆ Metric.ball (r • x) R ∩ E := by
    rintro y ⟨z, hz, rfl⟩
    refine ⟨?_, (hcone r hr z).mpr hz.2⟩
    change dist (r • z) (r • x) < R
    rw [dist_smul₀, Real.norm_of_nonneg hr.le]
    simpa only [mul_comm] using (lt_div_iff₀ hr).mp hz.1
  apply lt_of_lt_of_le _ (measure_mono (μ := volume) hs)
  rw [Measure.addHaar_smul_of_nonneg volume hr.le]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne' hp.ne'

theorem isCone_perimeterSupport {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (hcone : IsCone E) : IsCone (perimeterSupport E) := by
  have hcompl : IsCone Eᶜ := fun r hr x ↦ not_congr (hcone r hr x)
  have hforward (x : Euc n) {r : ℝ} (hr : 0 < r)
      (hx : x ∈ perimeterSupport E) : r • x ∈ perimeterSupport E := by
    rw [perimeterSupport_eq_phaseSupport_inter hE] at hx ⊢
    exact ⟨hcone.smul_mem_phaseSupport hx.1 hr, hcompl.smul_mem_phaseSupport hx.2 hr⟩
  intro r hr x
  constructor
  · intro hx
    have hh := hforward (r • x) (inv_pos.mpr hr) hx
    simpa only [inv_smul_smul₀ hr.ne'] using hh
  · exact hforward x hr

theorem IsCone.isPathConnected_perimeterSupport {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (hcone : IsCone E)
    (hvertex : (0 : Euc n) ∈ perimeterSupport E) :
    IsPathConnected (perimeterSupport E) := by
  have hc := isCone_perimeterSupport hE hcone
  have hs : StarConvex ℝ (0 : Euc n) (perimeterSupport E) := by
    intro x hx a b ha hb hab
    by_cases hb0 : b = 0
    · simpa [hb0] using hvertex
    · simpa only [smul_zero, zero_add] using (hc b (lt_of_le_of_ne hb (Ne.symm hb0)) x).mpr hx
  exact hs.isPathConnected hvertex

def NestedMinimizingConeMaximumObligation : Prop :=
  ∀ (n : ℕ), 8 ≤ n → ∀ (E F : Set (Euc n)),
    IsLocallyPerimeterMinimizing E → IsLocallyPerimeterMinimizing F →
    IsCone E → IsCone F → E ⊆ F →
    (0 : Euc n) ∈ perimeterSupport E → (0 : Euc n) ∈ perimeterSupport F →
    perimeterSupport E = perimeterSupport F

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPISingularHarnack
open RPI.Boundary

def radialDensityIntegrand {n : ℕ} (c : Euc n) (k : ℕ) (ψ : ℝ → ℝ)
    (t : ℝ) (x : Euc n) : ℝ := t ^ k * ψ (t ^ 2 * ‖x-c‖ ^ 2)

def radialDensityDerivative {n : ℕ} (c : Euc n) (k : ℕ) (ψ : ℝ → ℝ)
    (t : ℝ) (x : Euc n) : ℝ :=
  (k : ℝ) * t ^ (k-1) * ψ (t ^ 2 * ‖x-c‖ ^ 2) +
    t ^ k * deriv ψ (t ^ 2 * ‖x-c‖ ^ 2) * (2*t*‖x-c‖ ^ 2)

theorem radialDensityIntegrand_hasDerivAt {n : ℕ} (c : Euc n) (k : ℕ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (t : ℝ) (x : Euc n) :
    HasDerivAt (fun s ↦ radialDensityIntegrand c k ψ s x)
      (radialDensityDerivative c k ψ t x) t := by
  have hi : HasDerivAt (fun s : ℝ ↦ s^2 * ‖x-c‖^2) (2*t*‖x-c‖^2) t := by
    simpa using (hasDerivAt_pow 2 t).mul_const (‖x-c‖^2)
  have hh := (hasDerivAt_pow k t).mul
    (((hψ.differentiable (by simp)) _).hasDerivAt.comp t hi)
  convert hh using 1 <;> try rfl
  · dsimp [radialDensityDerivative]
    ring

theorem radialDensityIntegrand_continuous {n : ℕ} (c : Euc n) (k : ℕ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    Continuous (fun p : ℝ × Euc n ↦ radialDensityIntegrand c k ψ p.1 p.2) := by
  unfold radialDensityIntegrand
  fun_prop

theorem radialDensityDerivative_continuous {n : ℕ} (c : Euc n) (k : ℕ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    Continuous (fun p : ℝ × Euc n ↦ radialDensityDerivative c k ψ p.1 p.2) := by
  have hd := hψ.continuous_deriv (by simp)
  unfold radialDensityDerivative
  fun_prop

theorem radialDensity_integral_hasDerivAt {n : ℕ} (c : Euc n) (M : ℝ) (k : ℕ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (μ : Measure (Euc n)) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Metric.closedBall c M) (t : ℝ) :
    Integrable (radialDensityDerivative c k ψ t) μ ∧
    HasDerivAt (fun s ↦ ∫ x, radialDensityIntegrand c k ψ s x ∂μ)
      (∫ x, radialDensityDerivative c k ψ t x ∂μ) t := by
  have hcF (s : ℝ) : Continuous (radialDensityIntegrand c k ψ s) :=
    (radialDensityIntegrand_continuous c k hψ).comp (continuous_const.prodMk continuous_id)
  have hcD (s : ℝ) : Continuous (radialDensityDerivative c k ψ s) :=
    (radialDensityDerivative_continuous c k hψ).comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ := (isCompact_closedBall c M).exists_bound_of_continuousOn (hcF t).continuousOn
  have hFi : Integrable (radialDensityIntegrand c k ψ t) μ :=
    Integrable.of_bound (hcF t).aestronglyMeasurable C (hμ.mono (fun x hx ↦ hC x hx))
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_closedBall c M)).exists_bound_of_continuousOn
    ((radialDensityDerivative_continuous c k hψ).continuousOn :
      ContinuousOn _ (Icc (t-1) (t+1) ×ˢ Metric.closedBall c M))
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo (t-1) (t+1)) (bound := fun _ ↦ B) (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s ↦ (hcF s).aestronglyMeasurable) hFi
    (hcD t).aestronglyMeasurable ?_ (integrable_const B) (Eventually.of_forall ?_)
  · filter_upwards [hμ] with x hx
    intro s hs
    exact hB (s,x) ⟨⟨hs.1.le,hs.2.le⟩,hx⟩
  · intro x s _
    exact radialDensityIntegrand_hasDerivAt c k hψ s x

theorem tangentialDivergence_radialProfile {n : ℕ} (hn : 0 < n)
    (E : Set (Euc n)) (c : Euc n) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (t : ℝ) (x : Euc n) (hN : ‖approximateNormal E x‖ = 1) :
    tangentialDivergence E (fun y ↦ ψ (t^2 * ‖y-c‖^2) • (y-c)) x =
      (n-1 : ℕ) * ψ (t^2 * ‖x-c‖^2) +
        2*t^2*deriv ψ (t^2 * ‖x-c‖^2) *
          (‖x-c‖^2 - (inner ℝ (approximateNormal E x) (x-c))^2) := by
  have hf : ContDiff ℝ ∞ (fun y : Euc n ↦ ψ (t^2 * ‖y-c‖^2)) :=
    hψ.comp (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ)))
  have hV : Differentiable ℝ (fun y : Euc n ↦ y-c) :=
    differentiable_id.sub (differentiable_const c)
  rw [tangentialDivergence_smul E (hf.differentiable (by simp)) hV,
    tangentialDivergence_displacement E c x hN hn]
  have hd : fderiv ℝ (fun y : Euc n ↦ ψ (t^2 * ‖y-c‖^2)) x =
      (deriv ψ (t^2 * ‖x-c‖^2) * t^2 * 2) • innerSL ℝ (x-c) := by
    have hi := (((hasFDerivAt_id x).sub_const c).norm_sq).const_mul (t^2)
    have hh := ((hψ.differentiable (by simp)) _).hasDerivAt.comp_hasFDerivAt x hi
    convert hh.fderiv using 1 <;> try rfl
    ext v
    simp
    ring
  rw [tangentialGradient, inner_sub_left, real_inner_smul_left]
  simp only [inner_gradient_left, hd, smul_apply,
    innerSL_apply_apply, smul_eq_mul, real_inner_self_eq_norm_sq]
  rw [real_inner_comm (x-c) (approximateNormal E x)]
  ring

theorem radialProfile_tsupport {n : ℕ} (c : Euc n) {ψ : ℝ → ℝ}
    (hψz : ∀ s, 1 ≤ s → ψ s = 0) {t : ℝ} (ht : 0 < t) :
    tsupport (fun x : Euc n ↦ ψ (t^2 * ‖x-c‖^2)) ⊆ Metric.closedBall c (1/t) := by
  apply closure_minimal
  · intro x hx
    by_contra hh
    have hr : 1/t < ‖x-c‖ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hh
    have htr : 1 < t * ‖x-c‖ := by
      have := (div_lt_iff₀ ht).mp hr
      nlinarith
    have hsq : 1 ≤ t^2 * ‖x-c‖^2 := by nlinarith [sq_nonneg (t * ‖x-c‖ - 1)]
    exact hx (hψz _ hsq)
  · exact Metric.isClosed_closedBall

theorem minimizing_radialDensityDerivative_nonpos {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c : Euc n) {M : ℝ} (hM : 0 < M) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψz : ∀ s, 1 ≤ s → ψ s = 0) (hψd : ∀ s, deriv ψ s ≤ 0)
    {t : ℝ} (ht : 1/M < t) :
    (∫ x in Metric.ball c M, radialDensityDerivative c (n-1) ψ t x ∂perimeterMeasure E) ≤ 0 := by
  let μ := (perimeterMeasure E).restrict (Metric.ball c M)
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 c M hM⟩
  have hμ : ∀ᵐ x ∂μ, x ∈ Metric.closedBall c M :=
    (ae_restrict_mem measurableSet_ball).mono fun _ hx ↦ Metric.ball_subset_closedBall hx
  have hd := radialDensity_integral_hasDerivAt c M (n-1) hψ μ hμ t
  have ht0 : 0 < t := (one_div_pos.mpr hM).trans ht
  have htM : 1/t < M := (div_lt_iff₀ ht0).mpr (by
    have := (div_lt_iff₀ hM).mp ht
    nlinarith)
  let V : Euc n → Euc n := fun x ↦ ψ (t^2 * ‖x-c‖^2) • (x-c)
  have hf : ContDiff ℝ ∞ (fun x : Euc n ↦ ψ (t^2 * ‖x-c‖^2)) :=
    hψ.comp (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ)))
  have hV : ContDiff ℝ ∞ V := hf.smul (contDiff_id.sub contDiff_const)
  have hs : tsupport V ⊆ Metric.closedBall c (1/t) :=
    (tsupport_smul_subset_left _ _).trans (radialProfile_tsupport c hψz ht0)
  have hc : HasCompactSupport V :=
    (isCompact_closedBall c (1/t)).of_isClosed_subset (isClosed_tsupport _) hs
  have hz := minimizing_tangentialDivergence_integral_eq_zero hn hmin c hM hV hc
    (hs.trans (Metric.closedBall_subset_ball htM))
  have hi := (tangentialDivergence_integrable_ball_perimeter hmin c hM hV).const_mul (t^((n-1)-1))
  have hcmp : ∀ᵐ x ∂μ,
      radialDensityDerivative c (n-1) ψ t x ≤ t^((n-1)-1) * tangentialDivergence E V x := by
    filter_upwards [ae_restrict_of_ae (minimizing_halfspaceBlowup_ae hn hmin)] with x hx
    have hpow : t^(n-1) = t^((n-1)-1)*t := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n-1)]
    have heq : radialDensityDerivative c (n-1) ψ t x =
        t^((n-1)-1) * tangentialDivergence E V x +
        (2*t^((n-1)-1)*t^2*(inner ℝ (approximateNormal E x) (x-c))^2) *
          deriv ψ (t^2*‖x-c‖^2) := by
      dsimp [V, radialDensityDerivative]
      rw [tangentialDivergence_radialProfile (by omega) E c hψ t x hx.1, hpow]
      ring
    rw [heq]
    exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos (by positivity) (hψd _))
  have h := integral_mono_ae hd.1 hi hcmp
  rw [integral_const_mul] at h
  change _ ≤ _ * (∫ x in Metric.ball c M, tangentialDivergence E V x ∂perimeterMeasure E) at h
  simpa only [hz, mul_zero] using h

theorem minimizing_smoothedDensity_antitoneOn {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c : Euc n) {M : ℝ} (hM : 0 < M) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψz : ∀ s, 1 ≤ s → ψ s = 0) (hψd : ∀ s, deriv ψ s ≤ 0) :
    AntitoneOn (fun t ↦ ∫ x in Metric.ball c M,
      radialDensityIntegrand c (n-1) ψ t x ∂perimeterMeasure E) (Ioi (1/M)) := by
  let μ := (perimeterMeasure E).restrict (Metric.ball c M)
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 c M hM⟩
  have hμ : ∀ᵐ x ∂μ, x ∈ Metric.closedBall c M :=
    (ae_restrict_mem measurableSet_ball).mono fun _ hx ↦ Metric.ball_subset_closedBall hx
  have hd := fun t ↦ (radialDensity_integral_hasDerivAt c M (n-1) hψ μ hμ t).2
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi (1/M))
    (fun t _ ↦ (hd t).continuousAt.continuousWithinAt)
    (fun t _ ↦ (hd t).hasDerivWithinAt)
  intro t ht
  exact minimizing_radialDensityDerivative_nonpos hn hmin c hM hψ hψz hψd
    (by simpa only [interior_Ioi, mem_Ioi] using ht)

def densityProfile (j : ℕ) (s : ℝ) : ℝ :=
  Real.smoothTransition (((j : ℝ)+1)*(1-s))

theorem densityProfile_contDiff (j : ℕ) : ContDiff ℝ ∞ (densityProfile j) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))

theorem densityProfile_mem_Icc (j : ℕ) (s : ℝ) : densityProfile j s ∈ Icc (0:ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem densityProfile_zero (j : ℕ) {s : ℝ} (hs : 1 ≤ s) : densityProfile j s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

theorem densityProfile_deriv_nonpos (j : ℕ) (s : ℝ) : deriv (densityProfile j) s ≤ 0 := by
  have hm : Antitone (densityProfile j) := by
    intro a b hab
    apply Real.smoothTransition.monotone
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  exact hm.deriv_nonpos

theorem densityProfile_eventually_one {s : ℝ} (hs : s < 1) :
    ∀ᶠ j : ℕ in atTop, densityProfile j s = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1/(1-s))
  filter_upwards [eventually_ge_atTop N] with j hj
  apply Real.smoothTransition.one_of_one_le
  have hn : (N : ℝ) ≤ j := by exact_mod_cast hj
  have hdiv : 1/(1-s) < (j:ℝ)+1 := by linarith
  exact ((div_lt_iff₀ (by linarith : 0 < 1-s)).mp hdiv).le

theorem radialDensityIntegrand_tendsto {n : ℕ} (c : Euc n) (k : ℕ)
    {t : ℝ} (ht : 0 < t) (x : Euc n) :
    Tendsto (fun j ↦ radialDensityIntegrand c k (densityProfile j) t x) atTop
      (𝓝 ((Metric.ball c (1/t)).indicator (fun _ ↦ t^k) x)) := by
  by_cases hx : x ∈ Metric.ball c (1/t)
  · have hr : ‖x-c‖ < 1/t := by simpa [Metric.mem_ball, dist_eq_norm] using hx
    have htr : t*‖x-c‖ < 1 := by
      have := (lt_div_iff₀ ht).mp hr
      nlinarith
    have hq : t^2*‖x-c‖^2 < 1 := by
      have := mul_self_lt_mul_self (mul_nonneg ht.le (norm_nonneg (x-c))) htr
      nlinarith
    rw [indicator_of_mem hx]
    apply tendsto_const_nhds.congr'
    filter_upwards [densityProfile_eventually_one hq] with j hj
    simp [radialDensityIntegrand, hj]
  · have hr : 1/t ≤ ‖x-c‖ := by simpa [Metric.mem_ball, dist_eq_norm] using hx
    have htr : 1 ≤ t*‖x-c‖ := by
      have := (div_le_iff₀ ht).mp hr
      nlinarith
    have hq : 1 ≤ t^2*‖x-c‖^2 := by nlinarith [sq_nonneg (t*‖x-c‖-1)]
    rw [indicator_of_notMem hx]
    have heq : (fun j ↦ radialDensityIntegrand c k (densityProfile j) t x) = fun _ ↦ (0:ℝ) := by
      funext j
      simp [radialDensityIntegrand, densityProfile_zero j hq]
    rw [heq]
    exact tendsto_const_nhds

theorem radialDensity_integral_tendsto {n : ℕ}
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c : Euc n) {M : ℝ} (hM : 0 < M) {t : ℝ} (ht : 1/M < t) :
    Tendsto (fun j ↦ ∫ x in Metric.ball c M,
      radialDensityIntegrand c (n-1) (densityProfile j) t x ∂perimeterMeasure E) atTop
      (𝓝 (t^(n-1) * (perimeterMeasure E).real (Metric.ball c (1/t)))) := by
  let μ := (perimeterMeasure E).restrict (Metric.ball c M)
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 c M hM⟩
  have ht0 : 0 < t := (one_div_pos.mpr hM).trans ht
  have htM : 1/t < M := (div_lt_iff₀ ht0).mpr (by
    have := (div_lt_iff₀ hM).mp ht
    nlinarith)
  have hh := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ ↦ t^(n-1))
    (fun j ↦ ((radialDensityIntegrand_continuous c (n-1) (densityProfile_contDiff j)).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (integrable_const _) (fun j ↦ ae_of_all μ fun x ↦ ?_)
    (ae_of_all μ (radialDensityIntegrand_tendsto c (n-1) ht0))
  · have heq : (∫ x, (Metric.ball c (1/t)).indicator (fun _ ↦ t^(n-1)) x ∂μ) =
        t^(n-1) * (perimeterMeasure E).real (Metric.ball c (1/t)) := by
      rw [integral_indicator_const (t^(n-1)) measurableSet_ball, smul_eq_mul, mul_comm]
      congr 1
      change (μ (Metric.ball c (1/t))).toReal = _
      rw [Measure.restrict_apply measurableSet_ball,
        inter_eq_left.mpr (Metric.ball_subset_ball htM.le)]
      rfl
    rwa [heq] at hh
  · dsimp [radialDensityIntegrand]
    rw [abs_of_nonneg (mul_nonneg (by positivity) (densityProfile_mem_Icc j _).1)]
    exact mul_le_of_le_one_right (by positivity) (densityProfile_mem_Icc j _).2

theorem minimizing_perimeter_density_monotone {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E) (c : Euc n) :
    MonotoneOn (fun r : ℝ ↦ (perimeterMeasure E).real (Metric.ball c r) / r^(n-1)) (Ioi 0) := by
  intro r hr R hR hrR
  have hr0 : 0 < r := hr
  have hR0 : 0 < R := hR
  let M := 2*R
  have hM : 0 < M := by dsimp [M]; positivity
  have hRM : 1/M < 1/R := one_div_lt_one_div_of_lt hR0 (by dsimp [M]; linarith)
  have htr : 1/R ≤ 1/r := one_div_le_one_div_of_le hr0 hrR
  have hrM : 1/M < 1/r := hRM.trans_le htr
  have hseq (j : ℕ) := minimizing_smoothedDensity_antitoneOn hn hmin c hM
    (densityProfile_contDiff j) (fun s hs ↦ densityProfile_zero j hs)
    (densityProfile_deriv_nonpos j) hRM hrM htr
  have hh := le_of_tendsto_of_tendsto
    (radialDensity_integral_tendsto hmin c hM hrM)
    (radialDensity_integral_tendsto hmin c hM hRM) (Eventually.of_forall hseq)
  simpa [one_div, div_eq_mul_inv, mul_comm] using hh

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPISingularHarnack

theorem support_ray_inner_le_zero {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {x v w : Euc n} (hv : HasHalfspaceBlowup E x v)
    (hray : ∀ r : ℝ, 0 < r → r < 1 → x + r • w ∈ perimeterSupport E) :
    inner ℝ w v ≤ 0 := by
  by_contra hbad
  have ha : 0 < inner ℝ w v := lt_of_not_ge hbad
  let a := inner ℝ w v
  let δ := a / 4
  let A := ‖w‖ + δ + 1
  have hδ : 0 < δ := by dsimp [δ, a]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  let f : Euc n → ℝ := fun y ↦ |E.indicator (fun _ ↦ (1 : ℝ)) y -
    {z | inner ℝ (z - x) v < 0}.indicator (fun _ ↦ (1 : ℝ)) y|
  have hfm : Measurable f := by
    apply Measurable.abs
    exact (measurable_const.indicator hmin.1).sub
      (measurable_const.indicator (isOpen_lt
        ((continuous_id.sub continuous_const).inner continuous_const) continuous_const).measurableSet)
  have hfi (s : ℝ) : IntegrableOn f (Metric.ball x s) volume := by
    apply (integrableOn_const measure_ball_lt_top.ne (C := (1 : ℝ))).mono' hfm.aestronglyMeasurable
    apply ae_of_all
    intro y
    dsimp [f]
    by_cases he : y ∈ E <;> by_cases hh : inner ℝ (y - x) v < 0 <;> simp [he, hh]
  obtain ⟨ε, hε, hphase⟩ := minimizing_scaled_two_phase_volume_lower
    (Real.HolderConjugate.conjExponent (by exact_mod_cast hn : 1 < (n : ℝ)))
  have hlow (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
      ε * (r * δ) ^ n ≤ ∫ y in Metric.ball x (r * A), f y := by
    let B := Metric.closedBall (x + r • w) (r * δ)
    have hsub : B ⊆ Metric.ball x (r * A) := by
      intro y hy
      have ht := dist_triangle y (x + r • w) x
      have hd : dist (x + r • w) x = r * ‖w‖ := by
        simp [dist_eq_norm, norm_smul, abs_of_pos hr]
      rw [hd] at ht
      have hb : dist y (x + r • w) ≤ r * δ := hy
      change dist y x < r * A
      dsimp [A]
      nlinarith
    have hpos (y : Euc n) (hy : y ∈ B) : 0 < inner ℝ (y - x) v := by
      have hi := (abs_le.mp (abs_real_inner_le_norm (y - (x + r • w)) v)).1
      rw [hv.1, mul_one] at hi
      have hb : ‖y - (x + r • w)‖ ≤ r * δ := by
        simpa only [B, Metric.mem_closedBall, dist_eq_norm] using hy
      have he : inner ℝ (y - x) v = inner ℝ (y - (x + r • w)) v + r * a := by
        simp [a, inner_sub_left, inner_add_left, real_inner_smul_left]
        ring
      dsimp [δ] at hb
      rw [he]
      nlinarith
    have heq : (∫ y in B, f y) = volume.real (E ∩ B) := by
      calc
        (∫ y in B, f y) = ∫ y in B, E.indicator (fun _ ↦ (1 : ℝ)) y := by
          apply setIntegral_congr_fun measurableSet_closedBall
          intro y hy
          have hh : ¬ inner ℝ (y - x) v < 0 := not_lt.mpr (hpos y hy).le
          dsimp [f]
          by_cases he : y ∈ E <;> simp [he, hh]
        _ = volume.real (E ∩ B) := by
          simp only [integral_indicator_const _ hmin.1,
            measureReal_restrict_apply hmin.1, smul_eq_mul, mul_one]
    exact le_trans (hphase E hmin _ (hray r hr hr1) _ (mul_pos hr hδ)).1.le
      (heq ▸ setIntegral_mono_set (hfi _) (ae_of_all _ (fun y ↦ abs_nonneg _))
        (Eventually.of_forall hsub))
  have ht : Tendsto (fun r : ℝ ↦ r * A) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using ((tendsto_id : Tendsto (fun r : ℝ ↦ r) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds).mul_const A
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hA
  have hlim := hv.2.comp ht
  change Tendsto (fun r : ℝ ↦ ((r * A) ^ n)⁻¹ * ∫ y in Metric.ball x (r * A), f y)
    (𝓝[>] 0) (𝓝 0) at hlim
  have hb : ε * δ ^ n / A ^ n ≤ (0 : ℝ) := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with r hr hr1
    change 0 < r at hr
    have hl := hlow r hr hr1
    rw [mul_pow] at hl
    apply (div_le_iff₀ (pow_pos hA n)).mpr
    have he : (((r * A) ^ n)⁻¹ * ∫ y in Metric.ball x (r * A), f y) * A ^ n =
        (r ^ n)⁻¹ * ∫ y in Metric.ball x (r * A), f y := by
      rw [mul_pow]
      field_simp
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr (pow_pos hr n).le)
    convert hh using 1
    field_simp [ne_of_gt hr]
  have : 0 < ε * δ ^ n / A ^ n := div_pos (mul_pos hε (pow_pos hδ n)) (pow_pos hA n)
  linarith

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPISingularHarnack

theorem minimizing_cone_halfspace_radial_tangent {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E) (hcone : IsCone E)
    {x v : Euc n} (hx : x ∈ perimeterSupport E) (hv : HasHalfspaceBlowup E x v) :
    inner ℝ x v = 0 := by
  have hc := isCone_perimeterSupport hmin.1 hcone
  have hplus : inner ℝ x v ≤ 0 := support_ray_inner_le_zero hn hmin hv (by
    intro r hr _
    have hh := (hc (1 + r) (by linarith) x).mpr hx
    simpa only [add_smul, one_smul] using hh)
  have hminus : inner ℝ (-x) v ≤ 0 := support_ray_inner_le_zero hn hmin hv (by
    intro r _ hr
    have hh := (hc (1 - r) (by linarith) x).mpr hx
    rw [sub_smul, one_smul] at hh
    simpa only [smul_neg, sub_eq_add_neg] using hh)
  rw [inner_neg_left] at hminus
  linarith

theorem minimizing_cone_radial_tangent_ae {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E) (hcone : IsCone E) :
    ∀ᵐ x ∂perimeterMeasure E, inner ℝ x (approximateNormal E x) = 0 := by
  have hs : ∀ᵐ x ∂perimeterMeasure E, x ∈ perimeterSupport E := by
    rw [← perimeterMeasure_support]
    exact (perimeterMeasure E).support_mem_ae
  filter_upwards [minimizing_halfspaceBlowup_ae hn hmin, hs] with x hx hsx
  exact minimizing_cone_halfspace_radial_tangent hn hmin hcone hsx hx

end RPISingularHarnack

end

end OAI
