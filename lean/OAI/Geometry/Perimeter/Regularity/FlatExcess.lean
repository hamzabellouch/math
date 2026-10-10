import OAI.Geometry.Perimeter.Regularity.TendstoLintegralNormOfL2
import OAI.Geometry.Perimeter.Regularity.ExistsMinimizingDensityLimit
import OAI.Geometry.Perimeter.Regularity.LinearSchauder

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Pointwise
namespace RPISingularHarnack

theorem integral_abs_indicator_sub_eq_symmDiff {n : ℕ} {E F U : Set (Euc n)}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    (∫ x in U, |E.indicator (fun _ ↦ (1:ℝ)) x -
      F.indicator (fun _ ↦ (1:ℝ)) x|) = volume.real (symmDiff E F ∩ U) := by
  have hm : AEStronglyMeasurable (fun x ↦ E.indicator (fun _ ↦ (1:ℝ)) x -
      F.indicator (fun _ ↦ (1:ℝ)) x) (volume.restrict U) :=
    ((measurable_const.indicator hE).sub
      (measurable_const.indicator hF)).aestronglyMeasurable.restrict
  rw [measureReal_def, ← lintegral_indicator_difference hE hF,
    ← integral_norm_eq_lintegral_enorm hm]
  simp only [Real.norm_eq_abs]

theorem halfspace_perimeterSupport_subset_plane {n : ℕ} (v : Euc n) :
    perimeterSupport {x | inner ℝ x v < 0} ⊆ {x | inner ℝ x v = 0} := by
  let H : Set (Euc n) := {x | inner ℝ x v < 0}
  have hH : IsOpen H := isOpen_lt (continuous_id.inner continuous_const) continuous_const
  intro x hx
  have hx' := (Set.ext_iff.mp (perimeterSupport_eq_phaseSupport_inter hH.measurableSet) x).mp hx
  have hm : inner ℝ x v ≤ 0 := by
    have hc : closure H ⊆ {y | inner ℝ y v ≤ 0} :=
      closure_minimal (fun y hy ↦ show inner ℝ y v ≤ 0 from le_of_lt hy)
        (isClosed_le (continuous_id.inner continuous_const) continuous_const)
    exact hc (Measure.support_restrict_subset hx'.1).1
  have hp : 0 ≤ inner ℝ x v := by
    have hc : closure Hᶜ = Hᶜ := hH.isClosed_compl.closure_eq
    have hxC := (Measure.support_restrict_subset hx'.2).1
    rw [hc] at hxC
    exact not_lt.mp hxC
  exact le_antisymm hm hp

theorem halfspace_hasHalfspaceBlowup {n : ℕ} {v x : Euc n}
    (hv : ‖v‖ = 1) (hx : inner ℝ x v = 0) :
    HasHalfspaceBlowup {y | inner ℝ y v < 0} x v := by
  refine ⟨hv, ?_⟩
  have heq : {z | inner ℝ (z-x) v < 0} = {y | inner ℝ y v < 0} := by
    ext z
    simp only [mem_ofPred_eq, inner_sub_left, hx, sub_zero]
  simp only [heq, sub_self, abs_zero, integral_zero, mul_zero]
  exact tendsto_const_nhds

theorem HasHalfspaceBlowup.local_L1 {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {p v : Euc n} (hv : HasHalfspaceBlowup E p v)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (htr : Tendsto r atTop (𝓝 0)) :
    ∀ (x : Euc n) (R : ℝ), 0 < R →
      Tendsto (fun i ↦ volume.real (symmDiff (blownUpSet E p (r i))
        {z | inner ℝ z v < 0} ∩ Metric.closedBall x R)) atTop (𝓝 0) := by
  let H : Set (Euc n) := {z | inner ℝ z v < 0}
  let Hp : Set (Euc n) := {z | inner ℝ (z-p) v < 0}
  have hHp : MeasurableSet Hp :=
    (isOpen_lt ((continuous_id.sub continuous_const).inner continuous_const)
      continuous_const).measurableSet
  have he (i : ℕ) : blownUpSet (symmDiff E Hp) p (r i) =
      symmDiff (blownUpSet E p (r i)) H := by
    ext z
    have hz : p + r i • z ∈ Hp ↔ z ∈ H := by
      change inner ℝ (p + r i • z - p) v < 0 ↔ inner ℝ z v < 0
      rw [add_sub_cancel_left, real_inner_smul_left]
      constructor
      · intro hz
        exact (mul_neg_iff.mp hz).resolve_right (fun h ↦ (not_lt_of_ge (hr i).le) h.1) |>.2
      · exact mul_neg_of_pos_of_neg (hr i)
    simp only [blownUpSet, mem_preimage, mem_symmDiff, hz]
  have ht : Tendsto (fun t : ℝ ↦ (t^n)⁻¹ *
      volume.real (symmDiff E Hp ∩ Metric.ball p t)) (𝓝[>] 0) (𝓝 0) := by
    have hh := hv.2
    change Tendsto (fun t : ℝ ↦ (t^n)⁻¹ *
      ∫ x in Metric.ball p t, |E.indicator (fun _ ↦ (1:ℝ)) x -
        Hp.indicator (fun _ ↦ (1:ℝ)) x|) (𝓝[>] 0) (𝓝 0) at hh
    simpa only [integral_abs_indicator_sub_eq_symmDiff hE hHp] using hh
  have hcentral (S : ℝ) (hS : 0 < S) :
      Tendsto (fun i ↦ volume.real (symmDiff (blownUpSet E p (r i)) H ∩
        Metric.closedBall (0 : Euc n) S)) atTop (𝓝 0) := by
    have hscale : Tendsto (fun i ↦ r i * (S+1)) atTop (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.2
      refine ⟨?_, Eventually.of_forall fun i ↦ ?_⟩
      · simpa using htr.mul_const (S+1)
      · exact mul_pos (hr i) (by linarith)
    have ht' := (ht.comp hscale).const_mul ((S+1)^n)
    simp only [mul_zero] at ht'
    apply squeeze_zero (fun _ ↦ measureReal_nonneg) (fun i ↦ ?_) ht'
    rw [← he i, volumeReal_blownUpSet_closedBall (hE.symmDiff hHp) p (hr i)]
    calc
      (r i ^ n)⁻¹ * volume.real (symmDiff E Hp ∩ Metric.closedBall p (r i*S)) ≤
          (r i ^ n)⁻¹ * volume.real (symmDiff E Hp ∩ Metric.ball p (r i*(S+1))) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg (hr i).le _))
        apply measureReal_mono
          (inter_subset_inter_right _ (Metric.closedBall_subset_ball (by nlinarith [hr i])))
          (measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne)
      _ = (S+1)^n * ((r i*(S+1))^n)⁻¹ *
          volume.real (symmDiff E Hp ∩ Metric.ball p (r i*(S+1))) := by
        have hs1 : S+1 ≠ 0 := ne_of_gt (by linarith)
        rw [mul_pow, mul_inv]
        field_simp [pow_ne_zero n (hr i).ne', pow_ne_zero n hs1]
      _ = _ := by dsimp only [Function.comp_def]; ring
  intro x R hR
  have hS : 0 < ‖x‖ + R := by positivity
  have hsub : Metric.closedBall x R ⊆ Metric.closedBall (0 : Euc n) (‖x‖+R) := by
    intro z hz
    have htri := dist_triangle z x (0 : Euc n)
    have hz' := Metric.mem_closedBall.mp hz
    simp only [dist_zero_right] at htri ⊢
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using
      (htri.trans (by linarith : dist z x + ‖x‖ ≤ ‖x‖ + R)))
  exact squeeze_zero (fun _ ↦ measureReal_nonneg)
    (fun i ↦ measureReal_mono (inter_subset_inter_right _ hsub)
      (measure_ne_top_of_subset inter_subset_right
        (isCompact_closedBall (0 : Euc n) (‖x‖+R)).measure_ne_top))
    (hcentral (‖x‖+R) hS)

theorem HasHalfspaceBlowup.support_height {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {p v : Euc n} (hv : HasHalfspaceBlowup E p v)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (htr : Tendsto r atTop (𝓝 0))
    {C : Set (Euc n)} (hC : IsCompact C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ z ∈ perimeterSupport (blownUpSet E p (r i)) ∩ C,
      |inner ℝ z v| < ε := by
  let H : Set (Euc n) := {z | inner ℝ z v < 0}
  have hH : MeasurableSet H :=
    (isOpen_lt (continuous_id.inner continuous_const) continuous_const).measurableSet
  have hconv := hv.local_L1 hmin.1 r hr htr
  have hEm (i : ℕ) := locally_minimizing_blownUpSet hmin p (hr i)
  have hHm := locally_minimizing_of_local_L1_limit (by omega : 0 < n) hEm hH hconv
  filter_upwards [minimizing_supports_locally_converge hn _ hEm hHm hconv hC hε] with i hi
  intro z hz
  obtain ⟨y, hy, hzy⟩ := hi.1 z hz
  have hy0 := halfspace_perimeterSupport_subset_plane v hy
  have heq : inner ℝ z v = inner ℝ (z-y) v := by
    rw [inner_sub_left, hy0, sub_zero]
  rw [heq]
  calc
    |inner ℝ (z-y) v| ≤ ‖z-y‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ = dist z y := by rw [hv.1, mul_one, dist_eq_norm]
    _ < ε := hzy

def orientedTilt {n : ℕ} (E : Set (Euc n)) (v : Euc n) (U : Set (Euc n)) : ℝ :=
  ∫ x in U, ‖approximateNormal E x - v‖^2 ∂perimeterMeasure E

theorem orientedTilt_le_calibration_gap {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖ = 1) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {η : Euc n → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Metric.ball 0 b) (hb : ∀ x, η x ∈ Icc (0:ℝ) 1)
    (hone : ∀ x ∈ Metric.ball 0 a, η x = 1) :
    orientedTilt E v (Metric.ball 0 a) ≤
      2 * ((perimeter E (Metric.ball 0 b)).toReal -
        ∫ x in E, divergence (fun y ↦ η y • v) x) := by
  let μ := (perimeterMeasure E).restrict (Metric.ball 0 b)
  have hbf : 0 < b := ha.trans hab
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 0 b hbf⟩
  have hnb : ∀ x, |inner ℝ (approximateNormal E x) v| ≤ 1 := by
    intro x
    exact (abs_real_inner_le_norm _ _).trans (by
      rw [hv, mul_one]; exact approximateNormal_norm_le_one E x)
  have hp : ∀ x, |inner ℝ (approximateNormal E x) (η x • v)| ≤ 1 := by
    intro x
    rw [real_inner_smul_right, abs_mul, abs_of_nonneg (hb x).1]
    exact (mul_le_mul_of_nonneg_left (hnb x) (hb x).1).trans (by simpa using (hb x).2)
  have hnormal := measurable_approximateNormal hmin.1
  have hflux : Integrable (fun x ↦ inner ℝ (approximateNormal E x) (η x • v)) μ :=
    (integrable_const (1:ℝ)).mono'
      (hnormal.inner (hη.continuous.measurable.smul measurable_const)).aestronglyMeasurable
      (ae_of_all μ fun x ↦ by simpa only [Real.norm_eq_abs] using hp x)
  have htilt : Integrable (fun x ↦ ‖approximateNormal E x - v‖^2) μ := by
    apply (integrable_const (4:ℝ)).mono'
      ((hnormal.sub measurable_const).norm.pow_const 2).aestronglyMeasurable
    apply ae_of_all μ
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hbound : ‖approximateNormal E x-v‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by rw [hv]; linarith [approximateNormal_norm_le_one E x])
    change ‖approximateNormal E x-v‖^2 ≤ 4
    nlinarith [norm_nonneg (approximateNormal E x-v)]
  have hgg := minimizing_gaussGreen_local hn hmin (Metric.ball 0 b) Metric.isOpen_ball
    (hmin.2.1 0 b hbf).ne (fun x ↦ η x • v) (hη.smul contDiff_const)
    hc.smul_right (tsupport_smul_subset_left _ _ |>.trans hs)
  have hle : ∀ x, (Metric.ball (0:Euc n) a).indicator
      (fun x ↦ ‖approximateNormal E x-v‖^2) x ≤
        2 * (1 - inner ℝ (approximateNormal E x) (η x • v)) := by
    intro x
    by_cases hx : x ∈ Metric.ball (0:Euc n) a
    · rw [indicator_of_mem hx, hone x hx, one_smul, norm_sub_sq_real, hv]
      have hh := approximateNormal_norm_le_one E x
      have hpos := norm_nonneg (approximateNormal E x)
      nlinarith
    · rw [indicator_of_notMem hx]
      have hh := (le_abs_self _).trans (hp x)
      linarith
  have hh := integral_mono (htilt.indicator measurableSet_ball)
    (((integrable_const (1:ℝ)).sub hflux).const_mul 2) hle
  rw [integral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
    inter_eq_left.mpr (Metric.ball_subset_ball hab.le)] at hh
  rw [integral_const_mul] at hh
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (integrable_const _) hflux, integral_const] at hh
  change orientedTilt E v (Metric.ball 0 a) ≤ 2 * (μ.real univ * 1 - _) at hh
  have hmass : μ.real univ = (perimeter E (Metric.ball 0 b)).toReal := by
    simp [μ, measureReal_def]
  rw [hmass, mul_one] at hh
  exact hgg ▸ hh

theorem exists_halfspace_calibration {n : ℕ} (hn : 1 < n) {v : Euc n}
    (hv : ‖v‖ = 1)
    (hH : IsLocallyPerimeterMinimizing {x : Euc n | inner ℝ x v < 0})
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : Euc n → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Metric.ball 0 b ∧ (∀ x, η x ∈ Icc (0:ℝ) 1) ∧
      (∀ x ∈ Metric.ball 0 a, η x = 1) ∧
      (perimeter {x : Euc n | inner ℝ x v < 0} (Metric.ball 0 b)).toReal - ε <
        ∫ x in {x : Euc n | inner ℝ x v < 0}, divergence (fun y ↦ η y • v) x := by
  let H : Set (Euc n) := {x | inner ℝ x v < 0}
  let μ := (perimeterMeasure H).restrict (Metric.ball 0 b)
  have hb : 0 < b := ha.trans hab
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open H Metric.isOpen_ball]
    exact hH.2.1 0 b hb⟩
  let s : ℕ → ℝ := fun j ↦ (1-(1/2:ℝ)^(j+1))*b
  have hs0 (j : ℕ) : 0 < s j := by
    have hh : (1/2:ℝ)^(j+1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    exact mul_pos (sub_pos.mpr hh) hb
  have hsb (j : ℕ) : s j < b := by
    have hh : 0 < (1/2:ℝ)^(j+1) := pow_pos (by norm_num) _
    dsimp [s]
    nlinarith
  have ht : Tendsto s atTop (𝓝 b) := by
    have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).mul_const (1/2:ℝ)
    simpa only [s, pow_succ, zero_mul, sub_zero, one_mul] using
      (tendsto_const_nhds (x := (1:ℝ))).sub hpow |>.mul_const b
  obtain ⟨L, hL, hcut⟩ := exists_interior_cutoff_constant
  choose η hη hc hsupport hbound hone hgrad using
    (fun j ↦ hcut n H (s j) b (hs0 j) (hsb j))
  have hnH : ∀ᵐ x ∂μ, approximateNormal H x = v := by
    have hsupp : ∀ᵐ x ∂perimeterMeasure H, x ∈ perimeterSupport H := by
      rw [← perimeterMeasure_support H]
      exact (perimeterMeasure H).support_mem_ae
    filter_upwards [ae_restrict_of_ae hsupp] with x hx
    exact approximateNormal_eq_of_blowup hH.1
      (halfspace_hasHalfspaceBlowup hv (halfspace_perimeterSupport_subset_plane v hx))
  have heq (j : ℕ) : (∫ x in H, divergence (fun y ↦ η j y • v) x) = ∫ x, η j x ∂μ := by
    rw [minimizing_gaussGreen_local hn hH (Metric.ball 0 b) Metric.isOpen_ball
      (hH.2.1 0 b hb).ne (fun x ↦ η j x • v) ((hη j).smul contDiff_const)
      (hc j).smul_right (tsupport_smul_subset_left _ _ |>.trans (hsupport j))]
    apply integral_congr_ae
    filter_upwards [hnH] with x hx
    rw [hx, real_inner_smul_right, real_inner_self_eq_norm_sq, hv]
    ring
  have hlim : Tendsto (fun j ↦ ∫ x, η j x ∂μ) atTop
      (𝓝 ((perimeter H (Metric.ball 0 b)).toReal)) := by
    have hpoint : ∀ᵐ x ∂μ, Tendsto (fun j ↦ η j x) atTop (𝓝 (1:ℝ)) := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [ht.eventually (lt_mem_nhds (Metric.mem_ball.mp hx))] with j hj
      exact (hone j x (Metric.mem_ball.mpr hj)).symm
    have hh := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ ↦ (1:ℝ))
      (fun j ↦ (hη j).continuous.aestronglyMeasurable) (integrable_const _)
      (fun j ↦ ae_of_all μ fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbound j x).1]
        exact (hbound j x).2) hpoint
    simpa [μ, integral_const, measureReal_def] using hh
  have hnear := hlim.eventually
    (lt_mem_nhds (sub_lt_self _ hε))
  obtain ⟨j, hj, haj⟩ := (hnear.and (ht.eventually (lt_mem_nhds hab))).exists
  refine ⟨η j, hη j, hc j, hsupport j, hbound j, ?_, ?_⟩
  · intro x hx
    exact hone j x (Metric.ball_subset_ball haj.le hx)
  · rwa [heq j]

theorem HasHalfspaceBlowup.orientedTilt_tendsto {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {p v : Euc n} (hv : HasHalfspaceBlowup E p v)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (htr : Tendsto r atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun i ↦ orientedTilt (blownUpSet E p (r i)) v (Metric.ball 0 R))
      atTop (𝓝 0) := by
  let H : Set (Euc n) := {x | inner ℝ x v < 0}
  have hH : MeasurableSet H :=
    (isOpen_lt (continuous_id.inner continuous_const) continuous_const).measurableSet
  have hconv := hv.local_L1 hmin.1 r hr htr
  have hEm (i : ℕ) := locally_minimizing_blownUpSet hmin p (hr i)
  have hHm := locally_minimizing_of_local_L1_limit (by omega : 0 < n) hEm hH hconv
  obtain ⟨b, hnull, hRb, hbR⟩ := (minimizing_dense_null_spheres hHm (0:Euc n)).exists_between
    (show R < R+1 by linarith)
  have hb : 0 < b := hR.trans hRb
  have hmass := (ENNReal.tendsto_toReal (hHm.2.1 0 b hb).ne).comp
    (tendsto_minimizing_perimeter_ball_of_local_L1 (by omega : 0 < n) hEm hH hconv 0 hb hnull)
  apply tendsto_order.2
  constructor
  · intro A hA
    exact Eventually.of_forall fun i ↦ hA.trans_le (integral_nonneg fun _ ↦ sq_nonneg _)
  · intro ε hε
    obtain ⟨η, hη, hcη, hsη, hbη, honeη, hcal⟩ :=
      exists_halfspace_calibration hn hv.1 hHm hR hRb (by positivity : 0 < ε/4)
    have htflux := tendsto_setIntegral_of_local_symmDiff (fun i ↦ (hEm i).1) hH hconv
      (continuous_divergence (hη.smul contDiff_const))
      (hcη.smul_right.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_divergence_subset (fun y ↦ η y • v)))
    have htgap := (hmass.sub htflux).const_mul 2
    have hgap : 2 *((perimeter H (Metric.ball 0 b)).toReal -
        ∫ x in H, divergence (fun y ↦ η y • v) x) < ε := by linarith
    filter_upwards [htgap.eventually (gt_mem_nhds hgap)] with i hi
    exact (orientedTilt_le_calibration_gap hn (hEm i) hv.1 hR hRb
      hη hcη hsη hbη honeη).trans_lt hi

theorem HasHalfspaceBlowup.orientedTilt_tendsto_all_scales {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {p v : Euc n} (hv : HasHalfspaceBlowup E p v) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun r : ℝ ↦ orientedTilt (blownUpSet E p r) v (Metric.ball 0 R))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  apply Filter.tendsto_of_seq_tendsto
  intro r ht
  let s : ℕ → ℝ := fun i ↦ if 0 < r i then r i else 1
  have hs : ∀ i, 0 < s i := by
    intro i
    dsimp [s]
    split_ifs with h
    · exact h
    · norm_num
  have heq : s =ᶠ[atTop] r := by
    filter_upwards [ht.eventually self_mem_nhdsWithin] with i hi
    simp [s, hi]
  have hs0 : Tendsto s atTop (𝓝 (0:ℝ)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin ht).congr' heq.symm
  have hh := hv.orientedTilt_tendsto hn hmin s hs hs0 hR
  apply hh.congr'
  exact heq.fun_comp (fun a ↦ orientedTilt (blownUpSet E p a) v (Metric.ball 0 R))

theorem HasHalfspaceBlowup.support_height_all_scales {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {p v : Euc n} (hv : HasHalfspaceBlowup E p v)
    {C : Set (Euc n)} (hC : IsCompact C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ z ∈ perimeterSupport (blownUpSet E p r) ∩ C,
      |inner ℝ z v| < ε := by
  apply Filter.eventually_iff_seq_eventually.2
  intro r ht
  let s : ℕ → ℝ := fun i ↦ if 0 < r i then r i else 1
  have hs : ∀ i, 0 < s i := by
    intro i
    dsimp [s]
    split_ifs with h
    · exact h
    · norm_num
  have heq : s =ᶠ[atTop] r := by
    filter_upwards [ht.eventually self_mem_nhdsWithin] with i hi
    simp [s, hi]
  have hs0 : Tendsto s atTop (𝓝 (0:ℝ)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin ht).congr' heq.symm
  filter_upwards [hv.support_height hn hmin s hs hs0 hC hε, heq] with i hi he
  rwa [he] at hi

theorem HasHalfspaceBlowup.small_height_and_orientedTilt {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {p v : Euc n} (hv : HasHalfspaceBlowup E p v)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      (∀ z ∈ perimeterSupport (blownUpSet E p r) ∩ Metric.closedBall 0 R,
        |inner ℝ z v| < ε) ∧
      orientedTilt (blownUpSet E p r) v (Metric.ball 0 R) < ε := by
  exact (hv.support_height_all_scales hn hmin (isCompact_closedBall 0 R) hε).and
    ((hv.orientedTilt_tendsto_all_scales hn hmin hR).eventually (gt_mem_nhds hε))

theorem minimizing_height_caccioppoli {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c v : Euc n) (a : ℝ) {R : ℝ} (hR : 0 < R)
    {η : Euc n → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Metric.ball c R) :
    (∫ x in Metric.ball c R,
      η x ^ 2 * ‖tangentialGradient E (fun y ↦ inner ℝ v y - a) x‖ ^ 2
      ∂perimeterMeasure E) ≤
    4 * ∫ x in Metric.ball c R, (inner ℝ v x - a)^2 * ‖gradient η x‖^2
      ∂perimeterMeasure E := by
  let H : Euc n → ℝ := fun x ↦ inner ℝ v x - a
  have hH : ContDiff ℝ ∞ H := (contDiff_const.inner ℝ contDiff_id).sub contDiff_const
  have hgH (x : Euc n) : gradient H x = v := by
    apply HasGradientAt.gradient
    change HasFDerivAt H ((InnerProductSpace.toDual ℝ (Euc n)) v) x
    exact (innerSL ℝ v).hasFDerivAt.sub_const a
  let φ : Euc n → ℝ := fun x ↦ (η x * η x) * H x
  have hφ : ContDiff ℝ ∞ φ := (hη.mul hη).mul hH
  have hcφ : HasCompactSupport φ := (hc.mul_right).mul_right
  have hsφ : tsupport φ ⊆ Metric.ball c R :=
    tsupport_mul_subset_left.trans (tsupport_mul_subset_left.trans hs)
  let μ := (perimeterMeasure E).restrict (Metric.ball c R)
  let := perimeterMeasure_locallyFinite E hmin.2.1
  have : IsFiniteMeasure μ := ⟨by
    simp only [μ, Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 c R hR⟩
  have hgd : Continuous (gradient η) := continuous_iff_continuousAt.mpr fun x ↦
    RPI.Boundary.continuousAt_gradient_of_contDiffAt (hη.contDiffAt.of_le (by simp))
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hη.continuous
  have hM0 : 0 ≤ M := (norm_nonneg (η c)).trans (hM c)
  have hA : MemLp (fun x ↦ η x • tangentialGradient E H x) (2:ℝ≥0∞) μ := by
    apply MemLp.of_bound
      (hη.continuous.aestronglyMeasurable.smul
        (measurable_tangentialGradient hmin.1 (hH.of_le (by simp))).aestronglyMeasurable)
      (M * (2 * ‖v‖))
    apply ae_of_all μ
    intro x
    change ‖η x • tangentialGradient E H x‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul (hM x)
      ((tangentialGradient_norm_le_twice E H x).trans_eq (by rw [hgH]))
      (norm_nonneg _) hM0
  have hIA : Integrable (fun x ↦ η x^2 * ‖tangentialGradient E H x‖^2) μ := by
    simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using
      hA.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have hIB : Integrable (fun x ↦ H x^2 * ‖gradient η x‖^2) μ := by
    apply IntegrableOn.mono_set
      (ContinuousOn.integrableOn_compact (isCompact_closedBall c R)
        ((hH.continuous.pow 2).mul (hgd.norm.pow 2)).continuousOn)
      Metric.ball_subset_closedBall
  have hIJ : Integrable (fun x ↦ inner ℝ (tangentialGradient E φ x) v) μ :=
    (tangentialGradient_integrable_ball_perimeter hmin c hR
      (hφ.of_le (by simp))).inner_const v
  have hz := minimizing_tangentialGradient_integral_eq_zero_local hn hmin c hR hφ hcφ hsφ v
  have hp : ∀ᵐ x ∂μ,
      η x^2 * ‖tangentialGradient E H x‖^2 ≤
      2 * inner ℝ (tangentialGradient E φ x) v + 4 * (H x^2 * ‖gradient η x‖^2) := by
    filter_upwards [ae_restrict_of_ae (minimizing_halfspaceBlowup_ae hn hmin)] with x hx
    have hW : inner ℝ (tangentialGradient E H x) v =
        ‖tangentialGradient E H x‖^2 := by
      simp only [tangentialGradient, hgH, inner_sub_left, real_inner_smul_left,
        norm_sub_sq_real, norm_smul, Real.norm_eq_abs, sq_abs,
        real_inner_smul_right, hx.1, mul_one, real_inner_self_eq_norm_sq]
      rw [real_inner_comm (approximateNormal E x) v]
      ring
    have hG : inner ℝ (tangentialGradient E η x) v =
        inner ℝ (gradient η x) (tangentialGradient E H x) := by
      simp only [tangentialGradient, hgH, inner_sub_left, real_inner_smul_left,
        inner_sub_right, real_inner_smul_right]
      rw [real_inner_comm (approximateNormal E x) v]
      ring
    have hD : inner ℝ (tangentialGradient E φ x) v =
        η x^2 * ‖tangentialGradient E H x‖^2 +
        2 * η x * H x * inner ℝ (gradient η x) (tangentialGradient E H x) := by
      dsimp only [φ]
      rw [tangentialGradient_mul E ((hη.differentiable (by simp) x).fun_mul
        (hη.differentiable (by simp) x)) (hH.differentiable (by simp) x),
        tangentialGradient_mul E (hη.differentiable (by simp) x)
          (hη.differentiable (by simp) x)]
      simp only [inner_add_left, real_inner_smul_left, hW, hG]
      ring
    have hnn := sq_nonneg ‖η x • tangentialGradient E H x + (2 * H x) • gradient η x‖
    rw [norm_add_sq_real] at hnn
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, real_inner_smul_right] at hnn
    have hiComm := real_inner_comm (tangentialGradient E H x) (gradient η x)
    rw [← hiComm] at hnn
    rw [hD]
    nlinarith only [hnn]
  have hi := integral_mono_ae hIA ((hIJ.const_mul 2).add (hIB.const_mul 4)) hp
  simp only [Pi.add_apply] at hi
  rw [integral_add (hIJ.const_mul 2) (hIB.const_mul 4), integral_const_mul,
    integral_const_mul] at hi
  change (∫ x, η x^2 * ‖tangentialGradient E H x‖^2 ∂μ) ≤
    2 * (∫ x in Metric.ball c R, inner ℝ (tangentialGradient E φ x) v ∂perimeterMeasure E) + _ at hi
  rw [hz, mul_zero, zero_add] at hi
  exact hi

theorem minimizing_height_distribution {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c : Euc n) {R : ℝ} (hR : 0 < R) (v : Euc n) (a : ℝ)
    {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Metric.ball c R) :
    (∫ x in Metric.ball c R, (inner ℝ v x - a) *
      tangentialDivergence E (gradient φ) x ∂perimeterMeasure E) = 0 := by
  let H : Euc n → ℝ := fun x ↦ inner ℝ v x - a
  have hH : ContDiff ℝ ∞ H := (contDiff_const.inner ℝ contDiff_id).sub contDiff_const
  have hgH (x : Euc n) : gradient H x = v := by
    apply HasGradientAt.gradient
    change HasFDerivAt H ((InnerProductSpace.toDual ℝ (Euc n)) v) x
    exact (innerSL ℝ v).hasFDerivAt.sub_const a
  have hG := gradient_contDiff hφ
  have hcG := gradient_hasCompactSupport hcφ
  have hsG : tsupport (gradient φ) ⊆ Metric.ball c R := by
    exact (tsupport_comp_subset (g := (InnerProductSpace.toDual ℝ (Euc n)).symm)
      (map_zero _) (fderiv ℝ φ)).trans ((tsupport_fderiv_subset ℝ).trans hsφ)
  let V : Euc n → Euc n := fun x ↦ H x • gradient φ x
  have hV : ContDiff ℝ ∞ V := hH.smul (𝕜' := ℝ) hG
  have hcV : HasCompactSupport V := hcG.smul_left (f := H)
  have hsV : tsupport V ⊆ Metric.ball c R :=
    (tsupport_smul_subset_right H (gradient φ)).trans hsG
  have heq (x : Euc n) :
      H x * tangentialDivergence E (gradient φ) x =
        tangentialDivergence E V x - inner ℝ (tangentialGradient E φ x) v := by
    rw [show V = fun y ↦ H y • gradient φ y from rfl,
      tangentialDivergence_smul E (hH.differentiable (by simp))
        (hG.differentiable (by simp))]
    simp only [tangentialGradient, hgH, inner_sub_left, real_inner_smul_left]
    rw [real_inner_comm v (gradient φ x),
      real_inner_comm (approximateNormal E x) (gradient φ x),
      real_inner_comm (approximateNormal E x) v]
    ring
  change (∫ x in Metric.ball c R, H x * tangentialDivergence E (gradient φ) x ∂perimeterMeasure E) = 0
  simp_rw [heq]
  rw [integral_sub (tangentialDivergence_integrable_ball_perimeter hmin c hR hV)
    ((tangentialGradient_integrable_ball_perimeter hmin c hR
      (hφ.of_le (by simp))).inner_const v),
    minimizing_tangentialDivergence_integral_eq_zero hn hmin c hR hV hcV hsV,
    minimizing_tangentialGradient_integral_eq_zero_local hn hmin c hR hφ hcφ hsφ v,
    sub_self]

def planarDivergence {n : ℕ} (v : Euc n) (V : Euc n → Euc n) (x : Euc n) : ℝ :=
  divergence V x - inner ℝ v (fderiv ℝ V x v)

theorem normal_quadratic_difference_le {n : ℕ} (L : Euc n →L[ℝ] Euc n)
    {u v : Euc n} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    |inner ℝ u (L u) - inner ℝ v (L v)| ≤ 2 * ‖L‖ * ‖u-v‖ := by
  have he : inner ℝ u (L u) - inner ℝ v (L v) =
      inner ℝ (u-v) (L u) + inner ℝ v (L (u-v)) := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ |inner ℝ (u-v) (L u)| + |inner ℝ v (L (u-v))| := abs_add_le _ _
    _ ≤ ‖u-v‖ * (‖L‖ * ‖u‖) + ‖v‖ * (‖L‖ * ‖u-v‖) := by
      apply add_le_add
      · simpa only [Real.norm_eq_abs] using
          (norm_inner_le_norm (𝕜 := ℝ) (u-v) (L u)).trans
            (mul_le_mul_of_nonneg_left (L.le_opNorm u) (norm_nonneg _))
      · simpa only [Real.norm_eq_abs] using
          (norm_inner_le_norm (𝕜 := ℝ) v (L (u-v))).trans
            (mul_le_mul_of_nonneg_left (L.le_opNorm (u-v)) (norm_nonneg _))
    _ ≤ ‖u-v‖ * (‖L‖ * 1) + 1 * (‖L‖ * ‖u-v‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hu (norm_nonneg _)) (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_right hv (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

theorem normal_error_integral_le {n : ℕ} {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) (c : Euc n) {R : ℝ} (hR : 0 < R)
    (v : Euc n) :
    (∫ x in Metric.ball c R, ‖approximateNormal E x - v‖ ∂perimeterMeasure E) ≤
      Real.sqrt (orientedTilt E v (Metric.ball c R)) *
        Real.sqrt ((perimeter E (Metric.ball c R)).toReal) := by
  let μ := (perimeterMeasure E).restrict (Metric.ball c R)
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 c R hR⟩
  have hmem : MemLp (fun x ↦ ‖approximateNormal E x - v‖) (ENNReal.ofReal (2:ℝ)) μ := by
    apply MemLp.of_bound
      (((measurable_approximateNormal hmin.1).sub measurable_const).norm.aestronglyMeasurable)
      (1+‖v‖)
    exact ae_of_all μ fun x ↦ by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact (norm_sub_le _ _).trans (add_le_add (approximateNormal_norm_le_one E x) le_rfl)
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2:ℝ).HolderConjugate 2 from Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (ae_of_all μ fun _ ↦ norm_nonneg _) (ae_of_all μ fun _ ↦ (zero_le_one : (0:ℝ) ≤ 1))
    hmem (memLp_const (1:ℝ))
  simpa only [mul_one, Real.rpow_two, one_pow, integral_const, smul_eq_mul, mul_one,
    μ, Measure.real, Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball,
    ← Real.sqrt_eq_rpow, orientedTilt] using hh

theorem minimizing_height_planar_residual {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c : Euc n) {R : ℝ} (hR : 0 < R) {v : Euc n} (hv : ‖v‖ = 1) (a : ℝ)
    {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Metric.ball c R)
    {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hheight : ∀ x ∈ perimeterSupport E ∩ Metric.ball c R, |inner ℝ v x - a| ≤ A)
    (hderiv : ∀ x ∈ Metric.ball c R, ‖fderiv ℝ (gradient φ) x‖ ≤ K) :
    |∫ x in Metric.ball c R, (inner ℝ v x - a) *
      planarDivergence v (gradient φ) x ∂perimeterMeasure E| ≤
      2 * A * K * (Real.sqrt (orientedTilt E v (Metric.ball c R)) *
        Real.sqrt ((perimeter E (Metric.ball c R)).toReal)) := by
  let μ := (perimeterMeasure E).restrict (Metric.ball c R)
  let H : Euc n → ℝ := fun x ↦ inner ℝ v x - a
  let G := gradient φ
  have hg := gradient_contDiff hφ
  have hH : Continuous H := (continuous_const.inner continuous_id).sub continuous_const
  have := perimeterMeasure_locallyFinite E hmin.2.1
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 c R hR⟩
  have hbH : ∀ᵐ x ∂μ, |H x| ≤ A := by
    have hmm : ∀ᵐ x ∂perimeterMeasure E, x ∈ perimeterSupport E := by
      rw [← perimeterMeasure_support]; exact (perimeterMeasure E).support_mem_ae
    filter_upwards [ae_restrict_of_ae hmm, ae_restrict_mem measurableSet_ball] with x hx hx'
    exact hheight x ⟨hx, hx'⟩
  have hpcont : Continuous (planarDivergence v G) :=
    (continuous_divergence hg).sub
      (continuous_const.inner ((hg.continuous_fderiv (by simp)).clm_apply continuous_const))
  have hpint : Integrable (fun x ↦ H x * planarDivergence v G x) μ :=
    ((hH.mul hpcont).continuousOn.integrableOn_compact (isCompact_closedBall c R)).mono_set
      Metric.ball_subset_closedBall
  have htint : Integrable (fun x ↦ H x * tangentialDivergence E G x) μ :=
    (tangentialDivergence_integrable_ball_perimeter hmin c hR hg).bdd_mul
      hH.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hbH)
  have hiN : Integrable (fun x ↦ ‖approximateNormal E x-v‖) μ := by
    apply Integrable.of_bound
      (((measurable_approximateNormal hmin.1).sub measurable_const).norm.aestronglyMeasurable)
      2
    apply ae_of_all μ
    intro x
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by
      simp only [hv]; linarith [approximateNormal_norm_le_one E x])
  have heq : (∫ x, H x * planarDivergence v G x ∂μ) =
      ∫ x, H x * planarDivergence v G x - H x * tangentialDivergence E G x ∂μ := by
    rw [integral_sub hpint htint]
    have hz := minimizing_height_distribution hn hmin c hR v a hφ hcφ hsφ
    change (∫ x, H x * tangentialDivergence E G x ∂μ) = 0 at hz
    rw [hz, sub_zero]
  have hb : ∀ᵐ x ∂μ,
      |H x * planarDivergence v G x - H x * tangentialDivergence E G x| ≤
        (2*A*K) * ‖approximateNormal E x-v‖ := by
    filter_upwards [hbH, ae_restrict_mem measurableSet_ball] with x hx hxB
    have hq := normal_quadratic_difference_le (fderiv ℝ G x)
      (approximateNormal_norm_le_one E x) hv.le
    have haeq : H x * planarDivergence v G x - H x * tangentialDivergence E G x =
        H x * (inner ℝ (approximateNormal E x) (fderiv ℝ G x (approximateNormal E x)) -
          inner ℝ v (fderiv ℝ G x v)) := by
      dsimp [planarDivergence, tangentialDivergence]
      ring
    rw [haeq, abs_mul]
    calc
      _ ≤ A * (2 * ‖fderiv ℝ G x‖ * ‖approximateNormal E x-v‖) :=
        mul_le_mul hx hq (abs_nonneg _) hA
      _ ≤ A * (2 * K * ‖approximateNormal E x-v‖) := by
        apply mul_le_mul_of_nonneg_left _ hA
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (hderiv x hxB) (by norm_num)) (norm_nonneg _)
      _ = _ := by ring
  change |∫ x, H x * planarDivergence v G x ∂μ| ≤ _
  rw [heq]
  calc
    _ ≤ ∫ x, |H x * planarDivergence v G x - H x * tangentialDivergence E G x| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, (2*A*K) * ‖approximateNormal E x-v‖ ∂μ :=
      integral_mono_ae (hpint.sub htint).abs (hiN.const_mul _) hb
    _ = (2*A*K) * ∫ x, ‖approximateNormal E x-v‖ ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (normal_error_integral_le hmin c hR v)
      (mul_nonneg (mul_nonneg (by norm_num) hA) hK)

theorem horizontal_normal_le_height_projection {n : ℕ} {N v w : Euc n}
    (hN : ‖N‖ = 1) (hv : ‖v‖ = 1) (hw : inner ℝ v w = 0) :
    |inner ℝ N w| ≤ ‖v - (inner ℝ N v) • N‖ * ‖w‖ := by
  have he : inner ℝ (N - (inner ℝ N v) • v) w = inner ℝ N w := by
    simp [inner_sub_left, real_inner_smul_left, hw]
  have hs : ‖N - (inner ℝ N v) • v‖ ^ 2 =
      ‖v - (inner ℝ N v) • N‖ ^ 2 := by
    simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, sq_abs,
      real_inner_smul_right, hN, hv, one_pow, mul_one]
    rw [real_inner_comm v N]
  have hn : ‖N - (inner ℝ N v) • v‖ = ‖v - (inner ℝ N v) • N‖ := by
    nlinarith [norm_nonneg (N - (inner ℝ N v) • v),
      norm_nonneg (v - (inner ℝ N v) • N)]
  rw [← he]
  simpa only [Real.norm_eq_abs, hn] using
    norm_inner_le_norm (𝕜 := ℝ) (N - (inner ℝ N v) • v) w

theorem minimizing_horizontal_normal_square_le {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c : Euc n) {v w : Euc n} (hv : ‖v‖ = 1) (hw : inner ℝ v w = 0)
    (a : ℝ) {R : ℝ} (hR : 0 < R)
    {η : Euc n → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Metric.ball c R) :
    (∫ x in Metric.ball c R, (η x * inner ℝ (approximateNormal E x) w)^2
      ∂perimeterMeasure E) ≤
    4 * ‖w‖^2 * ∫ x in Metric.ball c R, (inner ℝ v x - a)^2 * ‖gradient η x‖^2
      ∂perimeterMeasure E := by
  let μ := (perimeterMeasure E).restrict (Metric.ball c R)
  let H : Euc n → ℝ := fun x ↦ inner ℝ v x-a
  have hH : ContDiff ℝ ∞ H := (contDiff_const.inner ℝ contDiff_id).sub contDiff_const
  have hgH (x : Euc n) : gradient H x = v := by
    apply HasGradientAt.gradient
    change HasFDerivAt H ((InnerProductSpace.toDual ℝ (Euc n)) v) x
    exact (innerSL ℝ v).hasFDerivAt.sub_const a
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 c R hR⟩
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hη.continuous
  have hM0 : 0 ≤ M := (norm_nonneg (η c)).trans (hM c)
  have hLI : Integrable (fun x ↦ (η x * inner ℝ (approximateNormal E x) w)^2) μ := by
    have hh : MemLp (fun x ↦ η x * inner ℝ (approximateNormal E x) w) 2 μ := by
      apply MemLp.of_bound
        (hη.continuous.aestronglyMeasurable.mul
          ((measurable_approximateNormal hmin.1).inner measurable_const).aestronglyMeasurable)
        (M * ‖w‖)
      apply ae_of_all μ
      intro x
      change ‖η x * inner ℝ (approximateNormal E x) w‖ ≤ _
      rw [norm_mul]
      have hb : ‖inner ℝ (approximateNormal E x) w‖ ≤ ‖w‖ :=
        (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (approximateNormal_norm_le_one E x) (norm_nonneg w))
      exact mul_le_mul (hM x) hb (norm_nonneg _) hM0
    simpa only [Real.norm_eq_abs, sq_abs] using hh.integrable_norm_pow
      (by norm_num : (2:ℕ) ≠ 0)
  have hRI : Integrable (fun x ↦ η x^2 * ‖tangentialGradient E H x‖^2) μ := by
    have hh : MemLp (fun x ↦ η x • tangentialGradient E H x) 2 μ := by
      apply MemLp.of_bound
        (hη.continuous.aestronglyMeasurable.smul
          (measurable_tangentialGradient hmin.1 (hH.of_le (by simp))).aestronglyMeasurable)
        (M * (2*‖v‖))
      apply ae_of_all μ
      intro x
      change ‖η x • tangentialGradient E H x‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul (hM x) ((tangentialGradient_norm_le_twice E H x).trans_eq
        (by rw [hgH])) (norm_nonneg _) hM0
    simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using
      hh.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have hp : ∀ᵐ x ∂μ, (η x * inner ℝ (approximateNormal E x) w)^2 ≤
      ‖w‖^2 * (η x^2 * ‖tangentialGradient E H x‖^2) := by
    filter_upwards [ae_restrict_of_ae (minimizing_halfspaceBlowup_ae hn hmin)] with x hx
    have hh := horizontal_normal_le_height_projection hx.1 hv hw
    change |inner ℝ (approximateNormal E x) w| ≤
      ‖v - (inner ℝ (approximateNormal E x) v) • approximateNormal E x‖ * ‖w‖ at hh
    have hsq := sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr hh
    rw [sq_abs, mul_pow] at hsq
    have hi := mul_le_mul_of_nonneg_left hsq (sq_nonneg (η x))
    rw [← real_inner_comm (approximateNormal E x) v] at hi
    simpa only [mul_pow, tangentialGradient, hgH, mul_assoc, mul_left_comm, mul_comm] using hi
  have hi := integral_mono_ae hLI (hRI.const_mul _) hp
  rw [integral_const_mul] at hi
  exact hi.trans (by
    have hh := mul_le_mul_of_nonneg_left
      (minimizing_height_caccioppoli hn hmin c v a hR hη hc hs) (sq_nonneg ‖w‖)
    convert hh using 1
    ring)

theorem integral_abs_le_of_quadratic_mean_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : MemLp f 2 μ) {L : ℝ} (hL : 0 ≤ L)
    (hq : (∫ x, f x^2 ∂μ) ≤ L^2 * (μ univ).toReal) :
    (∫ x, |f x| ∂μ) ≤ L * (μ univ).toReal := by
  have hpq : Real.HolderConjugate 2 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hm : MemLp (fun x ↦ |f x|) (ENNReal.ofReal (2:ℝ)) μ := by
    simpa only [ENNReal.ofReal_ofNat, Real.norm_eq_abs] using hf.norm
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (ae_of_all μ fun x ↦ abs_nonneg (f x))
    (ae_of_all μ fun _ ↦ (zero_le_one : (0:ℝ) ≤ 1)) hm (memLp_const (1:ℝ))
  have hs : Real.sqrt (∫ x, f x^2 ∂μ) ≤ L * Real.sqrt (μ univ).toReal := by
    calc
      _ ≤ Real.sqrt (L^2 * (μ univ).toReal) := Real.sqrt_le_sqrt hq
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL]
  have hh' : (∫ x, |f x| ∂μ) ≤ Real.sqrt (∫ x, f x^2 ∂μ) * Real.sqrt (μ univ).toReal := by
    simpa only [mul_one, Real.rpow_two, sq_abs, one_pow, integral_const, smul_eq_mul,
      mul_one, Measure.real, ← Real.sqrt_eq_rpow] using hh
  calc
    _ ≤ (L * Real.sqrt (μ univ).toReal) * Real.sqrt (μ univ).toReal :=
      hh'.trans (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _))
    _ = _ := by rw [mul_assoc, Real.mul_self_sqrt ENNReal.toReal_nonneg]

theorem minimizing_horizontal_normal_integral_le {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c : Euc n) {v w : Euc n} (hv : ‖v‖ = 1) (hw : inner ℝ v w = 0)
    (a : ℝ) {R : ℝ} (hR : 0 < R)
    {η : Euc n → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Metric.ball c R)
    {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hheight : ∀ x ∈ perimeterSupport E ∩ Metric.ball c R, |inner ℝ v x-a| ≤ A)
    (hgrad : ∀ x ∈ Metric.ball c R, ‖gradient η x‖ ≤ L) :
    (∫ x in Metric.ball c R, |η x * inner ℝ (approximateNormal E x) w|
      ∂perimeterMeasure E) ≤
      (2 * ‖w‖ * A * L) * (perimeter E (Metric.ball c R)).toReal := by
  let μ := (perimeterMeasure E).restrict (Metric.ball c R)
  have := perimeterMeasure_locallyFinite E hmin.2.1
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 c R hR⟩
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hη.continuous
  have hM0 : 0 ≤ M := (norm_nonneg (η c)).trans (hM c)
  have hf : MemLp (fun x ↦ η x * inner ℝ (approximateNormal E x) w) 2 μ := by
    apply MemLp.of_bound
      (hη.continuous.aestronglyMeasurable.mul
        ((measurable_approximateNormal hmin.1).inner measurable_const).aestronglyMeasurable)
      (M * ‖w‖)
    apply ae_of_all μ
    intro x
    change ‖η x * inner ℝ (approximateNormal E x) w‖ ≤ _
    rw [norm_mul]
    have hb : ‖inner ℝ (approximateNormal E x) w‖ ≤ ‖w‖ :=
      (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (approximateNormal_norm_le_one E x) (norm_nonneg w))
    exact mul_le_mul (hM x) hb (norm_nonneg _) hM0
  have hfi : Integrable (fun x ↦ (inner ℝ v x-a)^2 * ‖gradient η x‖^2) μ :=
    (((continuous_const.inner continuous_id).sub continuous_const).pow 2 |>.mul
      ((gradient_contDiff hη).continuous.norm.pow 2)).continuousOn.integrableOn_compact
      (isCompact_closedBall c R) |>.mono_set Metric.ball_subset_closedBall
  have hG : (∫ x, (inner ℝ v x-a)^2 * ‖gradient η x‖^2 ∂μ) ≤
      A^2 * L^2 * (μ univ).toReal := by
    have hsupp : ∀ᵐ x ∂μ, x ∈ perimeterSupport E := by
      apply ae_restrict_of_ae
      rw [← perimeterMeasure_support]
      exact (perimeterMeasure E).support_mem_ae
    have hb : ∀ᵐ x ∂μ, (inner ℝ v x-a)^2 * ‖gradient η x‖^2 ≤ A^2 * L^2 := by
      filter_upwards [hsupp, ae_restrict_mem measurableSet_ball] with x hx hxB
      have h₁ := (sq_le_sq₀ (abs_nonneg _) hA).mpr (hheight x ⟨hx,hxB⟩)
      rw [sq_abs] at h₁
      have h₂ := (sq_le_sq₀ (norm_nonneg _) hL).mpr (hgrad x hxB)
      exact mul_le_mul h₁ h₂ (sq_nonneg _) (sq_nonneg _)
    have hi := integral_mono_ae hfi (integrable_const (A^2*L^2)) hb
    simpa only [integral_const, smul_eq_mul, mul_comm, Measure.real] using hi
  have hq : (∫ x, (η x * inner ℝ (approximateNormal E x) w)^2 ∂μ) ≤
      (2*‖w‖*A*L)^2 * (μ univ).toReal := by
    have hh := minimizing_horizontal_normal_square_le hn hmin c hv hw a hR hη hc hs
    change (∫ x, (η x * inner ℝ (approximateNormal E x) w)^2 ∂μ) ≤
      4*‖w‖^2 * _ at hh
    apply hh.trans
    have hi := mul_le_mul_of_nonneg_left hG (by positivity : 0 ≤ 4*‖w‖^2)
    convert hi using 1
    ring
  have hh := integral_abs_le_of_quadratic_mean_bound μ hf
    (show 0 ≤ 2*‖w‖*A*L by positivity) hq
  simpa only [μ, Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball] using hh

theorem minimizing_horizontal_test_le {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c : Euc n) {v w : Euc n} (hv : ‖v‖ = 1) (hw : inner ℝ v w = 0)
    (a : ℝ) {R : ℝ} (hR : 0 < R)
    {η φ : Euc n → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Metric.ball c R) (hφ : ContDiff ℝ ∞ φ)
    (hbφ : ∀ x, |φ x| ≤ 1)
    {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hheight : ∀ x ∈ perimeterSupport E ∩ Metric.ball c R, |inner ℝ v x-a| ≤ A)
    (hgrad : ∀ x ∈ Metric.ball c R, ‖gradient η x‖ ≤ L) :
    |∫ x in E, fderiv ℝ (fun y ↦ η y * φ y) x w| ≤
      (2 * ‖w‖ * A * L) * (perimeter E (Metric.ball c R)).toReal := by
  let μ := (perimeterMeasure E).restrict (Metric.ball c R)
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 c R hR⟩
  have htest : (∫ x in E, fderiv ℝ (fun y ↦ η y * φ y) x w) =
      ∫ x, φ x * (η x * inner ℝ (approximateNormal E x) w) ∂μ := by
    rw [← divergence_scalar_direction ((hη.mul hφ).differentiable (by simp)) w,
      minimizing_gaussGreen_local hn hmin (Metric.ball c R) Metric.isOpen_ball
        (hmin.2.1 c R hR).ne (fun y ↦ (η y * φ y) • w) ((hη.mul hφ).smul contDiff_const)
        hc.mul_right.smul_right
        (tsupport_smul_subset_left _ _ |>.trans (tsupport_mul_subset_left.trans hs))]
    apply integral_congr_ae
    apply ae_of_all μ
    intro x
    simp only [real_inner_smul_right]
    ring
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hη.continuous
  have hM0 : 0 ≤ M := (norm_nonneg (η c)).trans (hM c)
  have hg : Integrable (fun x ↦ η x * inner ℝ (approximateNormal E x) w) μ := by
    apply Integrable.of_bound
      (hη.continuous.aestronglyMeasurable.mul
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
  have hφg : Integrable (fun x ↦ φ x * (η x * inner ℝ (approximateNormal E x) w)) μ :=
    hg.bdd_mul hφ.continuous.aestronglyMeasurable (ae_of_all μ fun x ↦ by
      simpa only [Real.norm_eq_abs] using hbφ x)
  rw [htest]
  calc
    _ ≤ ∫ x, |φ x * (η x * inner ℝ (approximateNormal E x) w)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, |η x * inner ℝ (approximateNormal E x) w| ∂μ := by
      apply integral_mono_ae hφg.abs hg.abs
      exact ae_of_all μ fun x ↦ by
        change |φ x * (η x * inner ℝ (approximateNormal E x) w)| ≤ |η x * inner ℝ (approximateNormal E x) w|
        rw [abs_mul]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hbφ x) (abs_nonneg _)
    _ ≤ _ := minimizing_horizontal_normal_integral_le hn hmin c hv hw a hR hη hc hs
      hA hL hheight hgrad

end RPISingularHarnack

end

end OAI
