import OAI.Geometry.Perimeter.Regularity.ConeRadialCap

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

def dilatedVolumeTest {n : ℕ} (φ : Euc n → ℝ) (t : ℝ) (x : Euc n) : ℝ :=
  t^n * φ (t • x)

def dilatedVolumeTestDerivative {n : ℕ} (φ : Euc n → ℝ) (t : ℝ) (x : Euc n) : ℝ :=
  (n : ℝ)*t^(n-1)*φ (t • x) + t^n * fderiv ℝ φ (t • x) x

theorem dilatedVolumeTest_hasDerivAt {n : ℕ} {φ : Euc n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (t : ℝ) (x : Euc n) :
    HasDerivAt (fun s ↦ dilatedVolumeTest φ s x) (dilatedVolumeTestDerivative φ t x) t := by
  have hp : HasDerivAt (fun s : ℝ ↦ s • x) x t := by
    simpa using (hasDerivAt_id t).smul_const x
  have hc := ((hφ.differentiable (by simp)) (t • x)).hasFDerivAt.comp_hasDerivAt t hp
  convert (hasDerivAt_pow n t).mul hc using 1 <;> rfl

theorem dilatedVolumeTest_continuous {n : ℕ} {φ : Euc n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) :
    Continuous (fun p : ℝ × Euc n ↦ dilatedVolumeTest φ p.1 p.2) := by
  unfold dilatedVolumeTest
  fun_prop

theorem dilatedVolumeTestDerivative_continuous {n : ℕ} {φ : Euc n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) :
    Continuous (fun p : ℝ × Euc n ↦ dilatedVolumeTestDerivative φ p.1 p.2) := by
  have hd := hφ.continuous_fderiv (by simp)
  unfold dilatedVolumeTestDerivative
  fun_prop

theorem dilatedVolumeTest_integral_hasDerivAt {n : ℕ} {φ : Euc n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (M : ℝ) (μ : Measure (Euc n)) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Metric.closedBall 0 M) (t : ℝ) :
    Integrable (dilatedVolumeTestDerivative φ t) μ ∧
    HasDerivAt (fun s ↦ ∫ x, dilatedVolumeTest φ s x ∂μ)
      (∫ x, dilatedVolumeTestDerivative φ t x ∂μ) t := by
  have hcF (s : ℝ) : Continuous (dilatedVolumeTest φ s) :=
    (dilatedVolumeTest_continuous hφ).comp (continuous_const.prodMk continuous_id)
  have hcD (s : ℝ) : Continuous (dilatedVolumeTestDerivative φ s) :=
    (dilatedVolumeTestDerivative_continuous hφ).comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0:Euc n) M).exists_bound_of_continuousOn (hcF t).continuousOn
  have hFi : Integrable (dilatedVolumeTest φ t) μ :=
    Integrable.of_bound (hcF t).aestronglyMeasurable C (hμ.mono (fun x hx ↦ hC x hx))
  have hcB : ContinuousOn (fun p : ℝ × Euc n ↦ dilatedVolumeTestDerivative φ p.1 p.2)
      (Icc (t-1) (t+1) ×ˢ Metric.closedBall 0 M) :=
    (dilatedVolumeTestDerivative_continuous hφ).continuousOn
  obtain ⟨B, hB⟩ := ((isCompact_Icc : IsCompact (Icc (t-1) (t+1))).prod
    (isCompact_closedBall (0:Euc n) M)).exists_bound_of_continuousOn hcB
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo (t-1) (t+1)) (bound := fun _ ↦ B) (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s ↦ (hcF s).aestronglyMeasurable) hFi
    (hcD t).aestronglyMeasurable ?_ (integrable_const B) (Eventually.of_forall ?_)
  · filter_upwards [hμ] with x hx
    intro s hs
    exact hB (s,x) ⟨⟨hs.1.le,hs.2.le⟩,hx⟩
  · intro x s _
    exact dilatedVolumeTest_hasDerivAt hφ s x

theorem dilatedVolumeTestDerivative_eq_divergence {n : ℕ} (hn : 0 < n)
    {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ) (t : ℝ) (x : Euc n) :
    dilatedVolumeTestDerivative φ t x =
      t^(n-1) * divergence (fun y ↦ φ (t • y) • y) x := by
  have hη : Differentiable ℝ (fun y : Euc n ↦ φ (t • y)) :=
    (hφ.differentiable (by simp)).comp (differentiable_id.const_smul t)
  have hp := divergence_smul hη (differentiable_id (𝕜 := ℝ) (E := Euc n)) x
  change divergence (fun y ↦ φ (t • y) • y) x = _ at hp
  rw [hp, inner_gradient_left]
  have hid : divergence (id : Euc n → Euc n) x = n := by
    simp [divergence, fderiv_id]
  have hc := (((hφ.differentiable (by simp)) (t • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul t)).fderiv
  simp only [Function.comp_def] at hc
  rw [hid]
  simp only [id_eq]
  have hDx : fderiv ℝ (fun y ↦ φ (t • y)) x x = t * fderiv ℝ φ (t • x) x := by
    rw [hc]
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  rw [hDx]
  unfold dilatedVolumeTestDerivative
  have hpow : t^n = t^(n-1)*t := by rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [hpow]
  ring

theorem minimizing_radial_divergence_eq_zero {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (hrad : ∀ᵐ x ∂perimeterMeasure E, inner ℝ (approximateNormal E x) x = 0)
    {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    (∫ x in E, divergence (fun y ↦ φ y • y) x) = 0 := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (0 : Euc n)).mp hcφ.isBounded
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsφ : tsupport φ ⊆ Metric.ball (0:Euc n) R :=
    hr.trans (Metric.ball_subset_ball (le_max_left _ _))
  let V : Euc n → Euc n := fun y ↦ φ y • y
  have hV : ContDiff ℝ ∞ V := hφ.smul contDiff_id
  have hs : tsupport V ⊆ tsupport φ := tsupport_smul_subset_left _ _
  have hc : HasCompactSupport V := hcφ.of_isClosed_subset (isClosed_tsupport _) hs
  rw [minimizing_gaussGreen_local hn hmin (Metric.ball 0 R) Metric.isOpen_ball
    (hmin.2.1 0 R hR).ne V hV hc (hs.trans hsφ)]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_of_ae hrad] with x hx
  simp only [V, real_inner_smul_right, hx, mul_zero, Pi.zero_apply]

theorem tsupport_dilation_subset_ball {n : ℕ} {φ : Euc n → ℝ} {R : ℝ}
    (hs : tsupport φ ⊆ Metric.ball (0:Euc n) R) {t : ℝ} (ht : 0 < t) :
    tsupport (fun x ↦ φ (t • x)) ⊆ Metric.ball (0:Euc n) (R/t) := by
  intro x hx
  have hh := hs (tsupport_comp_subset_preimage φ (continuous_id.const_smul t) hx)
  change t • x ∈ Metric.ball 0 R at hh
  simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.le] at hh ⊢
  exact (lt_div_iff₀ ht).mpr (by simpa only [mul_comm] using hh)

theorem dilatedVolumeTest_zero_outside {n : ℕ} {φ : Euc n → ℝ} {R M t : ℝ}
    (hs : tsupport φ ⊆ Metric.ball (0:Euc n) R) (ht : 0 < t) (hM : R/t ≤ M)
    {x : Euc n} (hx : x ∉ Metric.ball 0 M) :
    dilatedVolumeTest φ t x = 0 ∧ dilatedVolumeTestDerivative φ t x = 0 := by
  have htx : t • x ∉ tsupport φ := by
    intro h
    apply hx
    have hn := hs h
    have hn' : x ∈ Metric.ball (0:Euc n) (R/t) := by
      simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.le] at hn ⊢
      exact (lt_div_iff₀ ht).mpr (by simpa only [mul_comm] using hn)
    exact Metric.ball_subset_ball hM hn'
  have hz := image_eq_zero_of_notMem_tsupport htx
  have hd := fderiv_of_notMem_tsupport ℝ htx
  simp only [dilatedVolumeTest, dilatedVolumeTestDerivative, hz, hd,
    zero_apply, mul_zero, add_zero, and_self]

theorem minimizing_dilatedVolumeTestDerivative_integral_eq_zero {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (hrad : ∀ᵐ x ∂perimeterMeasure E, inner ℝ (approximateNormal E x) x = 0)
    {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    {t : ℝ} (ht : 0 < t) :
    (∫ x in E, dilatedVolumeTestDerivative φ t x) = 0 := by
  have hφt : ContDiff ℝ ∞ (fun x ↦ φ (t • x)) := hφ.comp (contDiff_id.const_smul t)
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (0:Euc n)).mp hcφ.isBounded
  have hs := tsupport_dilation_subset_ball hr ht
  have hct : HasCompactSupport (fun x ↦ φ (t • x)) :=
    (isCompact_closedBall (0:Euc n) (r/t)).of_isClosed_subset (isClosed_tsupport _)
      (hs.trans Metric.ball_subset_closedBall)
  simp_rw [dilatedVolumeTestDerivative_eq_divergence (by omega : 0<n) hφ,
    integral_const_mul]
  rw [minimizing_radial_divergence_eq_zero hn hmin hrad hφt hct, mul_zero]

theorem minimizing_dilatedVolumeTest_integral_hasDerivAt_zero {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (hrad : ∀ᵐ x ∂perimeterMeasure E, inner ℝ (approximateNormal E x) x = 0)
    {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ ∫ x in E, dilatedVolumeTest φ s x) 0 t := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (0:Euc n)).mp hcφ.isBounded
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsφ : tsupport φ ⊆ Metric.ball (0:Euc n) R :=
    hr.trans (Metric.ball_subset_ball (le_max_left _ _))
  let M := 2*R/t
  have hbound (s : ℝ) (hs : t/2 < s) : R/s ≤ M := by
    have hh := div_le_div_of_nonneg_left hR.le (half_pos ht) hs.le
    have he : R/(t/2) = M := by dsimp [M]; field_simp
    exact hh.trans_eq he
  let μ := (volume.restrict E).restrict (Metric.ball (0:Euc n) M)
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_ball]
    exact lt_of_le_of_lt (measure_mono inter_subset_left) measure_ball_lt_top⟩
  have hμ : ∀ᵐ x ∂μ, x ∈ Metric.closedBall 0 M :=
    (ae_restrict_mem measurableSet_ball).mono fun _ hx ↦ Metric.ball_subset_closedBall hx
  have hd := (dilatedVolumeTest_integral_hasDerivAt hφ M μ hμ t).2
  have he (s : ℝ) (hs : t/2 < s) :
      (∫ x, dilatedVolumeTest φ s x ∂μ) = ∫ x in E, dilatedVolumeTest φ s x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    exact (dilatedVolumeTest_zero_outside hsφ ((half_pos ht).trans hs) (hbound s hs) hx).1
  have hdE : (∫ x, dilatedVolumeTestDerivative φ t x ∂μ) =
      ∫ x in E, dilatedVolumeTestDerivative φ t x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    exact (dilatedVolumeTest_zero_outside hsφ ht (hbound t (by linarith)) hx).2
  rw [hdE, minimizing_dilatedVolumeTestDerivative_integral_eq_zero hn hmin hrad hφ hcφ ht] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds (show t/2 < t by linarith)] with s hs
  exact (he s hs).symm

theorem minimizing_volume_test_dilation_invariant {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (hrad : ∀ᵐ x ∂perimeterMeasure E, inner ℝ (approximateNormal E x) x = 0)
    {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    {t : ℝ} (ht : 0 < t) :
    t^n * (∫ x in E, φ (t • x)) = ∫ x in E, φ x := by
  have hd (s : ℝ) (hs : s ∈ Ioi (0:ℝ)) :=
    minimizing_dilatedVolumeTest_integral_hasDerivAt_zero hn hmin hrad hφ hcφ hs
  have hh := isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0:ℝ)).isPreconnected
    (fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs ↦ (hd s hs).deriv) (show t ∈ Ioi (0:ℝ) from ht)
      (show (1:ℝ) ∈ Ioi (0:ℝ) by norm_num)
  simpa only [dilatedVolumeTest, one_pow, one_smul, one_mul, integral_const_mul] using hh

theorem minimizing_dilation_ae_eq {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (hrad : ∀ᵐ x ∂perimeterMeasure E, inner ℝ (approximateNormal E x) x = 0)
    {t : ℝ} (ht : 0 < t) :
    {x : Euc n | t⁻¹ • x ∈ E} =ᵐ[volume] E := by
  let F : Set (Euc n) := {x | t⁻¹ • x ∈ E}
  have hF : MeasurableSet F := hmin.1.preimage (continuous_id.const_smul t⁻¹).measurable
  have he : ∀ᵐ x ∂volume, F.indicator (fun _ ↦ (1:ℝ)) x =
      E.indicator (fun _ ↦ (1:ℝ)) x := by
    apply ae_eq_of_integral_contDiff_smul_eq
      (indicator_one_locallyIntegrable hF) (indicator_one_locallyIntegrable hmin.1)
    intro φ hφ hcφ
    have hscale := Measure.integral_comp_smul_of_nonneg volume (F.indicator φ) t (hR := ht.le)
    have hi (x : Euc n) : (F.indicator φ) (t • x) =
        E.indicator (fun y ↦ φ (t • y)) x := by
      have hm : t • x ∈ F ↔ x ∈ E := by simp [F, inv_smul_smul₀ ht.ne']
      by_cases hx : x ∈ E
      · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hm.mpr hx)]
      · simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hm.mp hx)]
    simp_rw [hi] at hscale
    simp only [Euc, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
      integral_indicator hmin.1, integral_indicator hF] at hscale
    have htest := minimizing_volume_test_dilation_invariant hn hmin hrad hφ hcφ ht
    have hfint : (∫ x in F, φ x) = ∫ x in E, φ x := by
      rw [hscale] at htest
      simpa only [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht.ne'), one_mul] using htest
    have hprod (A : Set (Euc n)) (x : Euc n) :
        φ x • A.indicator (fun _ ↦ (1:ℝ)) x = A.indicator φ x := by
      by_cases hx : x ∈ A <;> simp [hx]
    simp_rw [hprod, integral_indicator hF, integral_indicator hmin.1]
    exact hfint
  apply Filter.eventuallyEqSet_iff.mpr
  filter_upwards [he] with x hx
  change x ∈ F ↔ x ∈ E
  by_cases hxF : x ∈ F <;> by_cases hxE : x ∈ E <;> simp_all

theorem minimizing_isCone_phaseSupport_of_radial_tangent {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (hrad : ∀ᵐ x ∂perimeterMeasure E, inner ℝ (approximateNormal E x) x = 0) :
    IsCone (volume.restrict E).support := by
  have hforward {x : Euc n} (hx : x ∈ (volume.restrict E).support)
      {r : ℝ} (hr : 0 < r) : r • x ∈ (volume.restrict E).support := by
    let F : Set (Euc n) := {y | r⁻¹ • y ∈ E}
    have hFE : F =ᵐ[volume] E := minimizing_dilation_ae_eq hn hmin hrad hr
    apply Metric.nhds_basis_ball.mem_measureSupport.mpr
    intro R hR
    rw [Measure.restrict_apply measurableSet_ball]
    have hp := Metric.nhds_basis_ball.mem_measureSupport.mp hx (R/r) (div_pos hR hr)
    rw [Measure.restrict_apply measurableSet_ball] at hp
    have hs : r • (Metric.ball x (R/r) ∩ E) ⊆ Metric.ball (r • x) R ∩ F := by
      rintro y ⟨z, hz, rfl⟩
      refine ⟨?_, ?_⟩
      · change dist (r • z) (r • x) < R
        rw [dist_smul₀, Real.norm_of_nonneg hr.le]
        simpa only [mul_comm] using (lt_div_iff₀ hr).mp hz.1
      · simpa only [F, mem_ofPred_eq, inv_smul_smul₀ hr.ne'] using hz.2
    have hnull : volume (Metric.ball (r • x) R ∩ F) =
        volume (Metric.ball (r • x) R ∩ E) := by
      apply measure_congr
      apply Filter.eventuallyEqSet_iff.mpr
      filter_upwards [hFE.mem_iff] with y hy
      exact and_congr_right (fun _ ↦ hy)
    rw [← hnull]
    apply lt_of_lt_of_le _ (measure_mono (μ := volume) hs)
    rw [Measure.addHaar_smul_of_nonneg volume hr.le]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne' hp.ne'
  intro r hr x
  constructor
  · intro hx
    have hh := hforward hx (inv_pos.mpr hr)
    simpa only [inv_smul_smul₀ hr.ne'] using hh
  · exact fun hx ↦ hforward hx hr

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

theorem minimizing_constant_density_conical_representative {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {a : ℝ} (ha : 0 ≤ a)
    (hdensity : ∀ r : ℝ, 0 < r → (perimeterMeasure E).real (Metric.ball 0 r) = a*r^(n-1)) :
    let K := (volume.restrict E).support
    IsClosed K ∧ E =ᵐ[volume] K ∧ IsLocallyPerimeterMinimizing K ∧ IsCone K ∧
      frontier K = perimeterSupport E := by
  let K := (volume.restrict E).support
  have hK : IsClosed K := Measure.isClosed_support
  have hp := Real.HolderConjugate.conjExponent (by exact_mod_cast hn : 1 < (n : ℝ))
  have hEK : E =ᵐ[volume] K := minimizing_ae_eq_phaseSupport hp hmin
  have hrad := minimizing_radial_tangent_of_constant_density hn hmin ha hdensity
  exact ⟨hK, hEK, hmin.of_ae hEK hK.measurableSet,
    minimizing_isCone_phaseSupport_of_radial_tangent hn hmin hrad,
    minimizing_frontier_phaseSupport hp hmin⟩

end RPISingularHarnack

end

end OAI
