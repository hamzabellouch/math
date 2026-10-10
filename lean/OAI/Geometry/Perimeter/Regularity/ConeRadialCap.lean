import OAI.Geometry.Perimeter.Regularity.SmulMemPhaseSupport

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

def coneRadialCap {n : ℕ} (R : ℝ) (x : Euc n) : ℝ :=
  expNegInvGlue (R ^ 2 - ‖x‖ ^ 2)

theorem coneRadialCap_contDiff {n : ℕ} (R : ℝ) :
    ContDiff ℝ ∞ (coneRadialCap (n := n) R) :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.norm_sq ℝ))

theorem coneRadialCap_tsupport {n : ℕ} {R : ℝ} (hR : 0 < R) :
    tsupport (coneRadialCap (n := n) R) ⊆ Metric.closedBall (0 : Euc n) R := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hh : 0 < R ^ 2 - ‖x‖ ^ 2 := by
    by_contra hh
    exact hx (expNegInvGlue.zero_of_nonpos (le_of_not_gt hh))
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg x]

theorem gradient_coneRadialCap {n : ℕ} (R : ℝ) (x : Euc n) :
    gradient (coneRadialCap R) x =
      (-2 * ((R ^ 2 - ‖x‖ ^ 2)⁻¹ ^ 2 * expNegInvGlue (R ^ 2 - ‖x‖ ^ 2))) • x := by
  have hg (s : ℝ) : HasDerivAt expNegInvGlue (s⁻¹ ^ 2 * expNegInvGlue s) s := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 s
  have hq := ((hasFDerivAt_id (𝕜 := ℝ) x).norm_sq).const_sub (R ^ 2)
  have hh := (hg (R ^ 2 - ‖x‖ ^ 2)).comp_hasFDerivAt x hq
  change HasFDerivAt (coneRadialCap R) _ x at hh
  apply (InnerProductSpace.toDual ℝ (Euc n)).injective
  rw [toDual_gradient, hh.fderiv]
  ext y
  simp only [smul_apply, neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, id_eq,
    innerSL_apply_apply, map_smul, InnerProductSpace.toDual_apply_apply,
    smul_eq_mul]
  ring

theorem minimizing_cone_support_in_halfspace_plane {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E) (hcone : IsCone E)
    (v : Euc n) (hside : ∀ x ∈ perimeterSupport E, 0 ≤ inner ℝ x v) :
    ∀ x ∈ perimeterSupport E, inner ℝ x v = 0 := by
  have hs : ∀ᵐ x ∂perimeterMeasure E, x ∈ perimeterSupport E := by
    rw [← perimeterMeasure_support]
    exact (perimeterMeasure E).support_mem_ae
  have h0 : ∀ᵐ x ∂perimeterMeasure E, 0 ≤ inner ℝ x v := hs.mono fun x hx ↦ hside x hx
  have hball (R : ℝ) (hR : 0 < R) :
      ∀ᵐ x ∂(perimeterMeasure E).restrict (Metric.ball 0 R), inner ℝ x v = 0 := by
    let φ : Euc n → ℝ := coneRadialCap R
    let b : Euc n → ℝ := fun x ↦ (R ^ 2 - ‖x‖ ^ 2)⁻¹ ^ 2 * expNegInvGlue (R ^ 2 - ‖x‖ ^ 2)
    let V : Euc n → Euc n := fun x ↦ φ x • v
    have hφ : ContDiff ℝ ∞ φ := coneRadialCap_contDiff R
    have htφ : HasCompactSupport φ := (isCompact_closedBall (0 : Euc n) R).of_isClosed_subset
      (isClosed_tsupport _) (coneRadialCap_tsupport hR)
    have hV : ContDiff ℝ ∞ V := hφ.smul contDiff_const
    have htV : HasCompactSupport V := htφ.smul_right
    have hVs : tsupport V ⊆ Metric.ball (0 : Euc n) (R + 1) :=
      (tsupport_smul_subset_left _ _).trans
        ((coneRadialCap_tsupport hR).trans (Metric.closedBall_subset_ball (by linarith)))
    have hdiv : ∀ᵐ x ∂perimeterMeasure E,
        tangentialDivergence E V x = -2 * (b x * inner ℝ x v) := by
      filter_upwards [minimizing_cone_radial_tangent_ae hn hmin hcone] with x hx
      rw [tangentialDivergence_smul E (hφ.differentiable (by simp)) (differentiable_const v)]
      have hc : tangentialDivergence E (fun _ : Euc n ↦ v) x = 0 := by
        simp [tangentialDivergence, divergence]
      rw [hc, mul_zero, zero_add, tangentialGradient, gradient_coneRadialCap]
      simp only [real_inner_smul_left, hx, mul_zero, zero_smul, sub_zero]
      dsimp [b]
      ring
    have hdf : Integrable (fun x ↦ b x * inner ℝ x v)
        ((perimeterMeasure E).restrict (Metric.ball 0 (R + 1))) := by
      have hh := (tangentialDivergence_integrable_ball_perimeter hmin 0 (by linarith : 0 < R + 1) hV).const_mul (-1/2 : ℝ)
      apply hh.congr
      filter_upwards [ae_restrict_of_ae hdiv] with x hx
      rw [hx]
      ring
    have hnn : ∀ᵐ x ∂(perimeterMeasure E).restrict (Metric.ball 0 (R + 1)),
        0 ≤ b x * inner ℝ x v := by
      filter_upwards [ae_restrict_of_ae h0] with x hx
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (expNegInvGlue.nonneg _)) hx
    have hint : (∫ x in Metric.ball (0 : Euc n) (R + 1), b x * inner ℝ x v ∂perimeterMeasure E) = 0 := by
      have hh := minimizing_tangentialDivergence_integral_eq_zero hn hmin 0
        (by linarith : 0 < R + 1) hV htV hVs
      rw [integral_congr_ae (ae_restrict_of_ae hdiv), integral_const_mul] at hh
      linarith
    have he := (integral_eq_zero_iff_of_nonneg_ae hnn hdf).mp hint
    have her : ∀ᵐ x ∂(perimeterMeasure E).restrict (Metric.ball 0 R), b x * inner ℝ x v = 0 :=
      ae_mono (Measure.restrict_mono (Metric.ball_subset_ball (by linarith)) le_rfl) he
    filter_upwards [her, ae_restrict_mem measurableSet_ball] with x hx hxr
    have hp : 0 < R ^ 2 - ‖x‖ ^ 2 := by
      have hh : ‖x‖ < R := by simpa using hxr
      nlinarith [norm_nonneg x]
    have hb : 0 < b x := mul_pos (sq_pos_of_pos (inv_pos.mpr hp)) (expNegInvGlue.pos_of_pos hp)
    exact (mul_eq_zero.mp hx).resolve_left hb.ne'
  have hae : ∀ᵐ x ∂perimeterMeasure E, inner ℝ x v = 0 := by
    let B (j : ℕ) := Metric.ball (0 : Euc n) (j + 1 : ℝ)
    have hcover : (⋃ j, B j) = univ := by
      apply eq_univ_of_forall
      intro x
      obtain ⟨j, hj⟩ := exists_nat_gt ‖x‖
      exact mem_iUnion.mpr ⟨j, by simpa [B] using (show ‖x‖ < (j : ℝ) + 1 by linarith)⟩
    have hh := (ae_restrict_iUnion_iff B (fun x ↦ inner ℝ x v = 0)).mpr
      (fun j ↦ hball (j + 1) (by positivity))
    simpa only [hcover, Measure.restrict_univ] using hh
  have hsup := Measure.support_subset_of_isClosed
    (isClosed_eq (continuous_id.inner continuous_const) continuous_const) hae
  rw [perimeterMeasure_support] at hsup
  exact hsup

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

theorem minimizing_cone_containing_halfspace_ae_eq {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E) (hcone : IsCone E)
    (hvertex : (0 : Euc n) ∈ perimeterSupport E)
    {v : Euc n} (hv : ‖v‖ = 1) (hinside : {x | inner ℝ x v < 0} ⊆ E) :
    E =ᵐ[volume] {x | inner ℝ x v < 0} := by
  let K := (volume.restrict E).support
  have hK : IsClosed K := Measure.isClosed_support
  have hP : IsOpen {x : Euc n | inner ℝ x v < 0} :=
    isOpen_lt (continuous_id.inner continuous_const) continuous_const
  have hPK : {x : Euc n | inner ℝ x v < 0} ⊆ K := by
    intro x hx
    apply Measure.interior_inter_support
    refine ⟨?_, ?_⟩
    · exact (interior_mono hinside) (hP.interior_eq.symm ▸ hx)
    · rw [Measure.support_eq_univ]; trivial
  have hPint : {x : Euc n | inner ℝ x v < 0} ⊆ interior K := by
    exact hP.interior_eq ▸ interior_mono hPK
  have hfK : frontier K = perimeterSupport E :=
    minimizing_frontier_phaseSupport
      (Real.HolderConjugate.conjExponent (by exact_mod_cast hn : 1 < (n : ℝ))) hmin
  have hside : ∀ x ∈ perimeterSupport E, 0 ≤ inner ℝ x v := by
    intro x hx
    by_contra hh
    have hi := hPint (lt_of_not_ge hh)
    rw [← hfK, frontier] at hx
    exact hx.2 hi
  have hplane := minimizing_cone_support_in_halfspace_plane hn hmin hcone v hside
  have hcover : {x : Euc n | 0 < inner ℝ x v} ⊆ interior K ∪ Kᶜ := by
    intro x hx
    by_cases hk : x ∈ K
    · left
      by_contra hi
      have hs : x ∈ perimeterSupport E := by
        rw [← hfK, frontier, hK.closure_eq]
        exact ⟨hk, hi⟩
      exact (ne_of_gt hx) (hplane x hs)
    · exact Or.inr hk
  have hc : IsPreconnected {x : Euc n | 0 < inner ℝ x v} := by
    have hh := (convex_halfSpace_gt (innerSL ℝ v).toLinearMap.isLinear (0 : ℝ)).isPreconnected
    change IsPreconnected {x : Euc n | 0 < inner ℝ v x} at hh
    simpa only [real_inner_comm v] using hh
  have hor := hc.subset_or_subset isOpen_interior hK.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hcover
  have hEK : E =ᵐ[volume] K := minimizing_ae_eq_phaseSupport
    (Real.HolderConjugate.conjExponent (by exact_mod_cast hn : 1 < (n : ℝ))) hmin
  rcases hor with hall | hnone
  · have hae : ∀ᵐ x ∂(volume : Measure (Euc n)), x ∈ K := by
      filter_upwards [ae_inner_ne_value hv 0] with x hx
      rcases lt_or_gt_of_ne hx with hn | hp
      · exact hPK hn
      · exact interior_subset (hall hp)
    have hKU : K = univ := by
      have hh := Measure.support_subset_of_isClosed hK hae
      rw [Measure.support_eq_univ] at hh
      exact eq_univ_iff_forall.mpr fun x ↦ hh trivial
    rw [← hfK, hKU, frontier_univ] at hvertex
    exact False.elim hvertex
  · apply hEK.trans
    apply Filter.eventuallyEqSet_iff.mpr
    filter_upwards [ae_inner_ne_value hv 0] with x hx
    rcases lt_or_gt_of_ne hx with hn | hp
    · exact iff_of_true (hPK hn) hn
    · exact iff_of_false (hnone hp) (not_lt.mpr hp.le)

theorem minimizing_cone_containing_halfspace_support_eq {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E) (hcone : IsCone E)
    (hvertex : (0 : Euc n) ∈ perimeterSupport E)
    {v : Euc n} (hv : ‖v‖ = 1) (hinside : {x | inner ℝ x v < 0} ⊆ E) :
    perimeterSupport E = perimeterSupport {x | inner ℝ x v < 0} :=
  perimeterSupport_eq_of_ae
    (minimizing_cone_containing_halfspace_ae_eq hn hmin hcone hvertex hv hinside)

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

theorem measure_eq_of_Iio_finite {μ ν : Measure ℝ}
    (hfin : ∀ a : ℝ, μ (Iio a) ≠ ⊤) (heq : ∀ a : ℝ, μ (Iio a) = ν (Iio a)) :
    μ = ν := by
  apply Measure.ext_of_Ico' μ ν
  · intro a b _
    exact ne_top_of_le_ne_top (hfin b) (measure_mono Ico_subset_Iio_self)
  · intro a b hab
    rw [← Iio_sdiff_Iio, measure_sdiff (Iio_subset_Iio hab.le)
      measurableSet_Iio.nullMeasurableSet (hfin a),
      measure_sdiff (Iio_subset_Iio hab.le) measurableSet_Iio.nullMeasurableSet
        (by rw [← heq a]; exact hfin a), heq a, heq b]

noncomputable def radialScaledMeasure {n : ℕ} (μ : Measure (Euc n)) (k : ℕ) (t : ℝ) : Measure ℝ :=
  ENNReal.ofReal (t^k) • μ.map (fun x ↦ t * ‖x‖)

theorem radialScaledMeasure_Iio {n k : ℕ} (μ : Measure (Euc n))
    {a t : ℝ} (ht : 0 < t) :
    radialScaledMeasure μ k t (Iio a) =
      ENNReal.ofReal (t^k) * μ (Metric.ball 0 (a/t)) := by
  have hm : Measurable (fun x : Euc n ↦ t * ‖x‖) := by fun_prop
  rw [radialScaledMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hm measurableSet_Iio]
  congr 2
  ext x
  simp only [mem_preimage, mem_Iio, Metric.mem_ball, dist_zero_right]
  rw [lt_div_iff₀ ht, mul_comm]

theorem radialScaledMeasure_eq_of_constant_density {n k : ℕ}
    (μ : Measure (Euc n)) (hfin : ∀ r : ℝ, 0 < r → μ (Metric.ball 0 r) ≠ ⊤)
    {a : ℝ} (ha : 0 ≤ a) (hdensity : ∀ r : ℝ, 0 < r → μ.real (Metric.ball 0 r) = a * r^k)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    radialScaledMeasure μ k s = radialScaledMeasure μ k t := by
  have hval (t : ℝ) (ht : 0 < t) (r : ℝ) :
      radialScaledMeasure μ k t (Iio r) = ENNReal.ofReal (a * (max r 0)^k) *
        (if 0 < r then 1 else 0) := by
    rw [radialScaledMeasure_Iio μ ht]
    by_cases hr : 0 < r
    · rw [ite_eq_left hr, mul_one, max_eq_left hr.le]
      have hrt : 0 < r/t := div_pos hr ht
      have hp := hdensity (r/t) hrt
      have he : μ (Metric.ball 0 (r/t)) = ENNReal.ofReal (a * (r/t)^k) := by
        rw [← hp, Measure.real, ENNReal.ofReal_toReal (hfin _ hrt)]
      rw [he, ← ENNReal.ofReal_mul' (mul_nonneg ha (pow_nonneg hrt.le _))]
      congr 1
      rw [div_pow]
      field_simp
    · rw [ite_eq_right hr, mul_zero, Metric.ball_eq_empty.mpr (div_nonpos_of_nonpos_of_nonneg
        (le_of_not_gt hr) ht.le), measure_empty, mul_zero]
  apply measure_eq_of_Iio_finite
  · intro r
    rw [hval s hs r]
    split_ifs <;> finiteness
  · intro r
    rw [hval s hs r, hval t ht r]

theorem radialDensity_integral_eq_pushforward {n k : ℕ} (μ : Measure (Euc n))
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) {t : ℝ} (ht : 0 < t) :
    (∫ x, radialDensityIntegrand 0 k ψ t x ∂μ) =
      ∫ s, ψ (s^2) ∂radialScaledMeasure μ k t := by
  have hm : Measurable (fun x : Euc n ↦ t * ‖x‖) := by fun_prop
  have hc : Continuous (fun s : ℝ ↦ ψ (s^2)) := by fun_prop
  rw [radialScaledMeasure, integral_smul_measure,
    integral_map_of_stronglyMeasurable hm hc.stronglyMeasurable,
    ENNReal.toReal_ofReal (pow_nonneg ht.le _)]
  simp only [radialDensityIntegrand, sub_zero, smul_eq_mul, mul_pow, integral_const_mul]

theorem radialDensity_integral_ball_eq {n k : ℕ} (μ : Measure (Euc n))
    {ψ : ℝ → ℝ} (hψz : ∀ s, 1 ≤ s → ψ s = 0)
    {M t : ℝ} (hM : 0 < M) (ht : 1/M < t) :
    (∫ x in Metric.ball (0 : Euc n) M, radialDensityIntegrand 0 k ψ t x ∂μ) =
      ∫ x, radialDensityIntegrand 0 k ψ t x ∂μ := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have ht0 : 0 < t := (one_div_pos.mpr hM).trans ht
  have htM : 1 < t*M := (div_lt_iff₀ hM).mp ht
  have hxM : M ≤ ‖x‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hx
  have h1 : 1 ≤ t*‖x‖ := by nlinarith
  have h2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) h1 2
  simp only [one_pow, mul_pow] at h2
  simp only [radialDensityIntegrand, sub_zero, hψz _ h2, mul_zero]

theorem minimizing_radialDensityDerivative_eq_zero_of_constant_density
    {n : ℕ} {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {a : ℝ} (ha : 0 ≤ a)
    (hdensity : ∀ r : ℝ, 0 < r → (perimeterMeasure E).real (Metric.ball 0 r) = a*r^(n-1))
    {M : ℝ} (hM : 0 < M) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψz : ∀ s, 1 ≤ s → ψ s = 0) {t : ℝ} (ht : 1/M < t) :
    (∫ x in Metric.ball 0 M, radialDensityDerivative 0 (n-1) ψ t x ∂perimeterMeasure E) = 0 := by
  let μ := (perimeterMeasure E).restrict (Metric.ball 0 M)
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 0 M hM⟩
  have hμ : ∀ᵐ x ∂μ, x ∈ Metric.closedBall 0 M :=
    (ae_restrict_mem measurableSet_ball).mono fun _ hx ↦ Metric.ball_subset_closedBall hx
  have hd := (radialDensity_integral_hasDerivAt 0 M (n-1) hψ μ hμ t).2
  have ht0 : 0 < t := (one_div_pos.mpr hM).trans ht
  have hfin (r : ℝ) (hr : 0 < r) : perimeterMeasure E (Metric.ball 0 r) ≠ ⊤ := by
    rw [perimeterMeasure_open E Metric.isOpen_ball]
    exact (hmin.2.1 0 r hr).ne
  have he (s : ℝ) (hs : 1/M < s) :
      (∫ x, radialDensityIntegrand 0 (n-1) ψ s x ∂μ) =
      ∫ x, radialDensityIntegrand 0 (n-1) ψ t x ∂μ := by
    have hs0 := (one_div_pos.mpr hM).trans hs
    change (∫ x in Metric.ball 0 M, _ ∂perimeterMeasure E) =
      ∫ x in Metric.ball 0 M, _ ∂perimeterMeasure E
    rw [radialDensity_integral_ball_eq _ hψz hM hs,
      radialDensity_integral_ball_eq _ hψz hM ht,
      radialDensity_integral_eq_pushforward _ hψ.continuous hs0,
      radialDensity_integral_eq_pushforward _ hψ.continuous ht0,
      radialScaledMeasure_eq_of_constant_density _ hfin ha hdensity hs0 ht0]
  have hdz : HasDerivAt (fun s ↦ ∫ x, radialDensityIntegrand 0 (n-1) ψ s x ∂μ) 0 t := by
    apply (hasDerivAt_const t (∫ x, radialDensityIntegrand 0 (n-1) ψ t x ∂μ)).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds ht] with s hs
    exact he s hs
  exact hd.unique hdz

theorem minimizing_radial_tangent_of_constant_density {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {a : ℝ} (ha : 0 ≤ a)
    (hdensity : ∀ r : ℝ, 0 < r → (perimeterMeasure E).real (Metric.ball 0 r) = a*r^(n-1)) :
    ∀ᵐ x ∂perimeterMeasure E, inner ℝ (approximateNormal E x) x = 0 := by
  let ψ : ℝ → ℝ := fun s ↦ expNegInvGlue (1-s)
  have hψ : ContDiff ℝ ∞ ψ := expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
  have hψz (s : ℝ) (hs : 1 ≤ s) : ψ s = 0 :=
    expNegInvGlue.zero_of_nonpos (by linarith)
  have hψd (s : ℝ) : deriv ψ s = -((1-s)⁻¹^2 * expNegInvGlue (1-s)) := by
    have hg : HasDerivAt expNegInvGlue ((1-s)⁻¹^2 * expNegInvGlue (1-s)) (1-s) := by
      simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 (1-s)
    simpa [ψ, Function.comp_def] using (hg.comp s ((hasDerivAt_id s).const_sub 1)).deriv
  have hlocal (R : ℝ) (hR : 0 < R) :
      ∀ᵐ x ∂(perimeterMeasure E).restrict (Metric.ball 0 R),
        inner ℝ (approximateNormal E x) x = 0 := by
    let M := 2*R
    let t := 1/R
    have hM : 0 < M := by dsimp [M]; positivity
    have ht0 : 0 < t := one_div_pos.mpr hR
    have ht : 1/M < t := one_div_lt_one_div_of_lt hR (by dsimp [M]; linarith)
    have htM : 1/t < M := by dsimp [t, M]; rw [one_div_one_div]; linarith
    let μ := (perimeterMeasure E).restrict (Metric.ball 0 M)
    have : IsFiniteMeasure μ := ⟨by
      rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
      exact hmin.2.1 0 M hM⟩
    have hμ : ∀ᵐ x ∂μ, x ∈ Metric.closedBall 0 M :=
      (ae_restrict_mem measurableSet_ball).mono fun _ hx ↦ Metric.ball_subset_closedBall hx
    let V : Euc n → Euc n := fun x ↦ ψ (t^2*‖x‖^2) • x
    have hV : ContDiff ℝ ∞ V :=
      (hψ.comp (contDiff_const.mul (contDiff_id.norm_sq (𝕜 := ℝ)))).smul contDiff_id
    have hp : tsupport (fun x : Euc n ↦ ψ (t^2*‖x‖^2)) ⊆ Metric.closedBall 0 (1/t) := by
      simpa only [sub_zero] using (radialProfile_tsupport (n := n) 0 hψz ht0)
    have hs : tsupport V ⊆ Metric.closedBall 0 (1/t) :=
      (tsupport_smul_subset_left (fun x : Euc n ↦ ψ (t^2*‖x‖^2))
        (id : Euc n → Euc n)).trans hp
    have hc : HasCompactSupport V :=
      (isCompact_closedBall (0 : Euc n) (1/t)).of_isClosed_subset (isClosed_tsupport _) hs
    have hdiv := minimizing_tangentialDivergence_integral_eq_zero hn hmin 0 hM hV hc
      (hs.trans (Metric.closedBall_subset_ball htM))
    have hD0 := minimizing_radialDensityDerivative_eq_zero_of_constant_density
      hmin ha hdensity hM hψ hψz ht
    have hDi := (radialDensity_integral_hasDerivAt 0 M (n-1) hψ μ hμ t).1
    have hVi := (tangentialDivergence_integrable_ball_perimeter hmin 0 hM hV).const_mul
      (t^((n-1)-1))
    let q : Euc n → ℝ := fun x ↦ t^((n-1)-1)*tangentialDivergence E V x -
      radialDensityDerivative 0 (n-1) ψ t x
    have hqi : Integrable q μ := hVi.sub hDi
    have hqformula : ∀ᵐ x ∂μ, q x =
        (2*t^((n-1)-1)*t^2*(inner ℝ (approximateNormal E x) x)^2) *
          ((1-t^2*‖x‖^2)⁻¹^2 * expNegInvGlue (1-t^2*‖x‖^2)) := by
      filter_upwards [ae_restrict_of_ae (minimizing_halfspaceBlowup_ae hn hmin)] with x hx
      have hpow : t^(n-1) = t^((n-1)-1)*t := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n-1)]
      have hvf := tangentialDivergence_radialProfile (by omega : 0<n) E 0 hψ t x hx.1
      simp only [sub_zero] at hvf
      dsimp [q, radialDensityDerivative]
      change t^((n-1)-1)*tangentialDivergence E V x - _ = _
      rw [show tangentialDivergence E V x = _ from hvf, hpow]
      simp only [sub_zero, hψd]
      ring
    have hqnonneg : ∀ᵐ x ∂μ, 0 ≤ q x := hqformula.mono fun x hx ↦ by
      rw [hx]
      exact mul_nonneg (by positivity)
        (mul_nonneg (sq_nonneg _) (expNegInvGlue.nonneg _))
    have hqint : (∫ x, q x ∂μ) = 0 := by
      rw [integral_sub hVi hDi, integral_const_mul]
      change _ * (∫ x in Metric.ball 0 M, tangentialDivergence E V x ∂perimeterMeasure E) - _ = 0
      rw [hdiv, hD0]
      ring
    have hqzero := (integral_eq_zero_iff_of_nonneg_ae hqnonneg hqi).mp hqint
    have hqz := (ae_restrict_iff' measurableSet_ball).mp hqzero
    have hqf := (ae_restrict_iff' measurableSet_ball).mp hqformula
    apply (ae_restrict_iff' measurableSet_ball).mpr
    filter_upwards [hqz, hqf] with x hxz hxf
    intro hx
    have hxM : x ∈ Metric.ball 0 M := Metric.ball_subset_ball (by dsimp [M]; linarith) hx
    have htx : t*‖x‖ < 1 := by
      have hxR : ‖x‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      simpa only [t, one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using (div_lt_one hR).mpr hxR
    have htx0 : 0 ≤ t*‖x‖ := mul_nonneg ht0.le (norm_nonneg x)
    have hspos : 0 < 1-t^2*‖x‖^2 := by
      nlinarith [mul_pos (sub_pos.mpr htx) (show 0 < 1+t*‖x‖ by linarith)]
    have hbpos : 0 < (1-t^2*‖x‖^2)⁻¹^2 * expNegInvGlue (1-t^2*‖x‖^2) :=
      mul_pos (sq_pos_of_pos (inv_pos.mpr hspos)) (expNegInvGlue.pos_of_pos hspos)
    have he := hxf hxM
    rw [hxz hxM] at he
    have hz : (inner ℝ (approximateNormal E x) x)^2 = 0 := by
      have hp : 0 < 2*t^((n-1)-1)*t^2 := by positivity
      exact (mul_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right hbpos.ne')).resolve_left hp.ne'
    exact sq_eq_zero_iff.mp hz
  let U : ℕ → Set (Euc n) := fun j ↦ Metric.ball 0 (j+1 : ℝ)
  have hcover : (⋃ j, U j) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨j, hj⟩ := exists_nat_gt ‖x‖
    exact mem_iUnion.mpr ⟨j, by simpa [U, Metric.mem_ball, dist_zero_right] using
      (show ‖x‖ < (j : ℝ)+1 by linarith)⟩
  have hall := (ae_restrict_iUnion_iff U
    (fun x ↦ inner ℝ (approximateNormal E x) x = 0)).mpr
      (fun j ↦ hlocal (j+1) (by positivity))
  simpa only [hcover, Measure.restrict_univ] using hall

end RPISingularHarnack

end

end OAI
