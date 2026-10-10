import OAI.Geometry.Perimeter.Regularity.IntegralDivergenceEqZero

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
open scoped Convolution

theorem integral_divergence_eq_zero_of_perimeter_eq_zero {n : ℕ}
    {E U : Set (Euc n)} (hP : perimeter E U = 0)
    {V : Euc n → Euc n} (hV : ContDiff ℝ ∞ V) (hc : HasCompactSupport V)
    (hs : tsupport V ⊆ U) : (∫ x in E, divergence V x) = 0 := by
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hV.continuous
  let a : ℝ := (|M| + 1)⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  let W : Euc n → Euc n := fun x ↦ a • V x
  have hW : PerimeterAdmissible U W := by
    have hsmul : ContDiff ℝ ∞ (fun z : Euc n ↦ a • z) :=
      (contDiff_const (c := a)).smul contDiff_id
    refine ⟨hsmul.comp hV, hc.comp_left (g := fun z : Euc n ↦ a • z) (smul_zero a), ?_, ?_⟩
    · exact (tsupport_smul_subset_right (fun _ ↦ a) V).trans hs
    · intro x
      simp only [W, norm_smul, Real.norm_of_nonneg ha.le]
      calc
        a * ‖V x‖ ≤ a * |M| := mul_le_mul_of_nonneg_left ((hM x).trans (le_abs_self M)) ha.le
        _ ≤ a * (|M| + 1) := mul_le_mul_of_nonneg_left (by linarith) ha.le
        _ = 1 := inv_mul_cancel₀ (by positivity)
  have hupper := integral_divergence_le_perimeter_real E U (by rw [hP]; simp) hW
  have hlower := integral_divergence_le_perimeter_real E U (by rw [hP]; simp)
    (perimeterAdmissible_neg hW)
  have hd : divergence W = fun x ↦ a * divergence V x := by
    funext x
    rw [divergence_smul (differentiable_const a) (hV.differentiable (by simp))]
    simp
  rw [hd, integral_const_mul, hP, ENNReal.toReal_zero] at hupper
  rw [divergence_neg (hW.1.differentiable (by simp))] at hlower
  simp only [Pi.neg_apply] at hlower
  rw [integral_neg, hd,
    integral_const_mul, hP, ENNReal.toReal_zero] at hlower
  nlinarith

theorem convolution_fderiv_eq_zero_of_perimeter_eq_zero {n : ℕ}
    {E U : Set (Euc n)} (hE : MeasurableSet E) (hP : perimeter E U = 0)
    {k : Euc n → ℝ} (hk : ContDiff ℝ ∞ k) (hck : HasCompactSupport k)
    (x : Euc n) (hs : ∀ y, x - y ∈ tsupport k → y ∈ U) :
    fderiv ℝ (E.indicator (fun _ ↦ (1 : ℝ)) ⋆[lsmul ℝ ℝ, volume] k) x = 0 := by
  let χ : Euc n → ℝ := E.indicator (fun _ ↦ 1)
  have hχ : LocallyIntegrable χ volume := indicator_one_locallyIntegrable hE
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by simp)
  rw [(hck.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hχ hk1 x).fderiv]
  ext v
  rw [convolution_precompR_apply (lsmul ℝ ℝ) hχ (hck.fderiv ℝ)
    (hk.continuous_fderiv (by simp))]
  let a : Euc n → ℝ := fun y ↦ k (x - y)
  let V : Euc n → Euc n := fun y ↦ a y • v
  have ha : ContDiff ℝ ∞ a := hk.comp (contDiff_const.sub contDiff_id)
  have hca : HasCompactSupport a := hck.comp_homeomorph (Homeomorph.subLeft x)
  have hsV : tsupport V ⊆ U := by
    apply (tsupport_smul_subset_left a (fun _ ↦ v)).trans
    intro y hy
    apply hs y
    exact (tsupport_comp_subset_preimage k (continuous_const.sub continuous_id)) hy
  have hd : divergence V = fun y ↦ -fderiv ℝ k (x - y) v := by
    funext y
    rw [divergence_smul (ha.differentiable (by simp)) (differentiable_const v)]
    simp only [divergence, fderiv_fun_const, Pi.zero_apply, zero_apply, inner_zero_right, Finset.sum_const_zero,
      mul_zero, zero_add, inner_gradient_left]
    have h := ((hk.differentiable (by simp) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))).fderiv
    simpa only [a, Function.comp_def, sub_apply, zero_apply, id_apply, zero_sub,
      ContinuousLinearMap.comp_apply, neg_apply, map_neg] using congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L v) h
  have hz := integral_divergence_eq_zero_of_perimeter_eq_zero hP
    (ha.smul (contDiff_const (c := v))) hca.smul_right hsV
  change (∫ x in E, divergence V x) = 0 at hz
  rw [hd, integral_neg, neg_eq_zero] at hz
  change (∫ t, χ t * fderiv ℝ k (x - t) v) = 0
  have heq : (fun t ↦ χ t * fderiv ℝ k (x - t) v) =
      E.indicator (fun t ↦ fderiv ℝ k (x - t) v) := by
    funext t
    by_cases ht : t ∈ E <;> simp [χ, ht]
  rw [heq, integral_indicator hE]
  exact hz

theorem volume_inter_eq_zero_or_compl_of_perimeter_eq_zero {n : ℕ}
    {E : Set (Euc n)} (hE : MeasurableSet E) (c : Euc n) {R : ℝ} (hR : 0 < R)
    (hP : perimeter E (Metric.ball c R) = 0) :
    volume (E ∩ Metric.ball c (R / 2)) = 0 ∨
      volume (Eᶜ ∩ Metric.ball c (R / 2)) = 0 := by
  let χ : Euc n → ℝ := E.indicator (fun _ ↦ 1)
  let u : ℕ → Euc n → ℝ := c1Mollify χ
  have hχ : LocallyIntegrable χ volume := indicator_one_locallyIntegrable hE
  have hflip : (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip = lsmul ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    exact mul_comm b a
  have hu_eq : ∀ j, u j = χ ⋆[lsmul ℝ ℝ, volume] (c1Mollifier j).normed volume := by
    intro j
    change (c1Mollifier j).normed volume ⋆[lsmul ℝ ℝ, volume] χ = _
    rw [← convolution_flip, hflip]
  have hu : ∀ j, ContDiff ℝ ∞ (u j) := fun j ↦
    (c1Mollifier j).hasCompactSupport_normed.contDiff_convolution_left _
      (c1Mollifier j).contDiff_normed hχ
  have hconst : ∀ᶠ j in atTop, ∀ x ∈ Metric.ball c (R / 2),
      ∀ y ∈ Metric.ball c (R / 2), u j x = u j y := by
    have hsmall : ∀ᶠ j in atTop, (c1Mollifier (n := n) j).rOut < R / 2 :=
      c1Mollifier_radius_tendsto.eventually (gt_mem_nhds (by positivity))
    filter_upwards [hsmall] with j hj
    have hzero : (Metric.ball c (R / 2)).EqOn (fderiv ℝ (u j)) 0 := by
      intro x hx
      rw [hu_eq j]
      apply convolution_fderiv_eq_zero_of_perimeter_eq_zero hE hP
        (c1Mollifier j).contDiff_normed (c1Mollifier j).hasCompactSupport_normed x
      intro y hy
      rw [(c1Mollifier j).tsupport_normed_eq] at hy
      have hxy : dist y x ≤ (c1Mollifier (n := n) j).rOut := by
        simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero, norm_sub_rev] using hy
      exact (dist_triangle y x c).trans_lt (by linarith [Metric.mem_ball.mp hx])
    intro x hx y hy
    exact Metric.isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball c (R / 2)).isPreconnected
      ((hu j).differentiable (by simp)).differentiableOn hzero hx hy
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun j ↦ u j x) atTop (𝓝 (χ x)) := by
    apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      c1Mollifier_radius_tendsto (K := 2) _ hχ
    apply Eventually.of_forall
    intro j
    dsimp [c1Mollifier]
    linarith
  by_contra hn
  push Not at hn
  obtain ⟨x, hx, hlimx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hn.1
    (hlim.filter_mono (ae_mono Measure.restrict_le_self))
  obtain ⟨y, hy, hlimy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hn.2
    (hlim.filter_mono (ae_mono Measure.restrict_le_self))
  have hxy : (fun j ↦ u j x) =ᶠ[atTop] (fun j ↦ u j y) :=
    hconst.mono fun j hj ↦ hj x hx.2 y hy.2
  have hlimxy := tendsto_nhds_unique hlimx (hlimy.congr' hxy.symm)
  have : (1 : ℝ) = 0 := by
    simpa only [χ, indicator_of_mem hx.1, indicator_of_notMem hy.1] using hlimxy
  exact one_ne_zero this

theorem perimeterSupport_eq_phaseSupport_inter {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) :
    perimeterSupport E = (volume.restrict E).support ∩ (volume.restrict Eᶜ).support := by
  ext x
  constructor
  · intro hx
    have hphase : ∀ F : Set (Euc n), MeasurableSet F → x ∈ perimeterSupport F →
        x ∈ (volume.restrict F).support := by
      intro F hF hxF
      apply (Metric.nhds_basis_ball.mem_measureSupport (μ := volume.restrict F)).mpr
      intro r hr
      apply pos_iff_ne_zero.mpr
      intro hz
      rw [Measure.restrict_apply measurableSet_ball, inter_comm] at hz
      have hpz := raw_perimeter_eq_zero_of_volume_inter_eq_zero measurableSet_ball hz
      exact (hxF r hr).ne' hpz
    exact ⟨hphase E hE hx, hphase Eᶜ hE.compl
      (by simpa only [perimeterSupport_compl hE] using hx)⟩
  · rintro ⟨hxE, hxEc⟩ r hr
    apply pos_iff_ne_zero.mpr
    intro hpz
    rcases volume_inter_eq_zero_or_compl_of_perimeter_eq_zero hE x hr hpz with hz | hz
    · have hpos := (Metric.nhds_basis_ball.mem_measureSupport (μ := volume.restrict E)).mp hxE
        (r / 2) (by positivity)
      rw [Measure.restrict_apply measurableSet_ball, inter_comm] at hpos
      exact hpos.ne' hz
    · have hpos := (Metric.nhds_basis_ball.mem_measureSupport (μ := volume.restrict Eᶜ)).mp hxEc
        (r / 2) (by positivity)
      rw [Measure.restrict_apply measurableSet_ball, inter_comm] at hpos
      exact hpos.ne' hz

theorem minimizing_frontier_phaseSupport {n : ℕ} {p : ℝ}
    (hp : Real.HolderConjugate (n : ℝ) p) {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) :
    frontier (volume.restrict E).support = perimeterSupport E := by
  let K : Set (Euc n) := (volume.restrict E).support
  have hK : IsClosed K := Measure.isClosed_support
  have hEK : E =ᵐ[volume] K := minimizing_ae_eq_phaseSupport hp hmin
  have hEcKc : Eᶜ =ᵐ[volume] Kᶜ := by
    apply Filter.eventuallyEqSet_iff.mpr
    filter_upwards [hEK.mem_iff] with x hx
    exact not_congr hx
  have hKc : (volume.restrict Kᶜ).support = closure Kᶜ := by
    apply le_antisymm (Measure.support_restrict_subset.trans inter_subset_left)
    apply closure_minimal _ Measure.isClosed_support
    intro x hx
    apply Measure.interior_inter_support
    exact ⟨(hK.isOpen_compl.interior_eq).symm ▸ hx, by rw [Measure.support_eq_univ]; trivial⟩
  have hμ : (volume : Measure (Euc n)).restrict Eᶜ = volume.restrict Kᶜ :=
    Measure.restrict_congr_set hEcKc
  rw [perimeterSupport_eq_phaseSupport_inter hmin.1, hμ, hKc,
    frontier_eq_closure_inter_closure, hK.closure_eq]

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack
open ContinuousLinearMap

theorem chord_half_norm_sub_le {n : ℕ} {f : Euc n → ℝ}
    (hf : ContDiff ℝ 1 f) (c x y : Euc n) {R : ℝ}
    (hx : x ∈ Metric.closedBall c R) (hy : y ∈ Metric.closedBall c R) :
    ‖f x - f ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)‖ ≤
      2 * R * ∫ t in (1 / 2 : ℝ)..1, ‖fderiv ℝ f (t • x + (1 - t) • y)‖ := by
  let z : ℝ → Euc n := fun t ↦ t • x + (1 - t) • y
  have hz : ∀ t, HasDerivAt z (x - y) t := by
    intro t
    simpa [z, sub_eq_add_neg, Pi.add_def] using
      ((hasDerivAt_id t).smul_const x).add
        (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const y)
  have hdf : ∀ t, HasDerivAt (fun t ↦ f (z t)) (fderiv ℝ f (z t) (x - y)) t := fun t ↦
    (hf.differentiable one_ne_zero (z t)).hasFDerivAt.comp_hasDerivAt t (hz t)
  have hxy : ‖x - y‖ ≤ 2 * R := by
    have hh := (dist_triangle x c y).trans (add_le_add (Metric.mem_closedBall.mp hx)
      (by simpa only [dist_comm] using Metric.mem_closedBall.mp hy))
    simpa only [dist_eq_norm, two_mul] using hh
  have hD : Continuous (fun t ↦ ‖fderiv ℝ f (z t)‖) :=
    ((hf.continuous_fderiv one_ne_zero).comp (by fun_prop)).norm
  have hi := norm_sub_le_integral_of_norm_deriv_le_of_le (a := (1 / 2 : ℝ))
    (b := 1) (f := fun t ↦ f (z t)) (B := fun t ↦ 2 * R * ‖fderiv ℝ f (z t)‖) (by norm_num)
    (hf.continuous.comp (by fun_prop)).continuousOn
    (fun t _ ↦ (hdf t).differentiableAt.differentiableWithinAt)
    (ae_of_all _ fun t _ ↦ by
      rw [(hdf t).deriv]
      exact ((fderiv ℝ f (z t)).le_opNorm (x - y)).trans
        (by nlinarith [norm_nonneg (fderiv ℝ f (z t))]))
    ((continuous_const.mul hD).intervalIntegrable _ _)
  simpa only [z, Function.comp_def, one_smul, sub_self, zero_smul, add_zero, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    intervalIntegral.integral_const_mul] using hi

theorem chord_half_integral_le {n : ℕ} {G : Euc n → ℝ}
    (hG : Continuous G) (hG0 : ∀ x, 0 ≤ G x) (c y : Euc n) {R t : ℝ}
    (hy : y ∈ Metric.closedBall c R) (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    (∫ x in Metric.closedBall c R, G (t • x + (1 - t) • y)) ≤
      2 ^ n * ∫ x in Metric.closedBall c R, G x := by
  let B := Metric.closedBall c R
  let g : Euc n → ℝ := B.indicator G
  have hg : Integrable g volume :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (hG.continuousOn.integrableOn_compact (isCompact_closedBall c R))
  have hg0 : ∀ x, 0 ≤ g x := fun x ↦ indicator_nonneg (fun x _ ↦ hG0 x) x
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  have hga : Integrable (fun x ↦ g (t • x + (1 - t) • y)) volume :=
    (hg.comp_add_right ((1 - t) • y)).comp_smul ht0.ne'
  have heq : ∀ x ∈ B, G (t • x + (1 - t) • y) = g (t • x + (1 - t) • y) := by
    intro x hx
    have hz : t • x + (1 - t) • y ∈ B :=
      (convex_closedBall c R) hx hy ht0.le (sub_nonneg.mpr ht.2) (by ring)
    exact (indicator_of_mem hz G).symm
  calc
    (∫ x in B, G (t • x + (1 - t) • y)) =
        ∫ x in B, g (t • x + (1 - t) • y) :=
      setIntegral_congr_fun measurableSet_closedBall heq
    _ ≤ ∫ x, g (t • x + (1 - t) • y) :=
      setIntegral_le_integral hga (ae_of_all _ fun x ↦ hg0 _)
    _ = (t ^ n)⁻¹ * ∫ x in B, G x := by
      rw [Measure.integral_comp_smul_of_nonneg volume
        (fun z ↦ g (z + (1 - t) • y)) t (hR := ht0.le)]
      rw [integral_add_right_eq_self, integral_indicator measurableSet_closedBall]
      simp only [Euc, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, B]
    _ ≤ 2 ^ n * ∫ x in B, G x := by
      apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun x ↦ hG0 x)
      have hh : (t ^ n)⁻¹ ≤ ((1 / 2 : ℝ) ^ n)⁻¹ :=
        inv_anti₀ (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _) (pow_le_pow_left₀ (by norm_num) ht.1 _)
      simpa only [inv_pow, one_div, inv_inv] using hh

theorem integrated_chord_half_le {n : ℕ} {f : Euc n → ℝ}
    (hf : ContDiff ℝ 1 f) (c y : Euc n) {R : ℝ}
    (hy : y ∈ Metric.closedBall c R) :
    (∫ x in Metric.closedBall c R, ‖f x - f ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)‖) ≤
      (2 * R) * (2 ^ n * ∫ x in Metric.closedBall c R, ‖fderiv ℝ f x‖) := by
  let B := Metric.closedBall c R
  let I := Icc (1 / 2 : ℝ) 1
  let G : Euc n → ℝ := fun x ↦ ‖fderiv ℝ f x‖
  let F : Euc n × ℝ → ℝ := fun p ↦ G (p.2 • p.1 + (1 - p.2) • y)
  have hG : Continuous G := (hf.continuous_fderiv one_ne_zero).norm
  have hF : Continuous F := hG.comp (by fun_prop)
  have hiF : Integrable F ((volume.restrict B).prod (volume.restrict I)) := by
    rw [Measure.prod_restrict]
    exact hF.continuousOn.integrableOn_compact ((isCompact_closedBall c R).prod isCompact_Icc)
  have hR : 0 ≤ 2 * R := by nlinarith [Metric.mem_closedBall.mp hy, dist_nonneg (x := y) (y := c)]
  have hp : IntegrableOn
      (fun x ↦ ‖f x - f ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)‖) B volume :=
    (hf.continuous.sub (hf.continuous.comp (by fun_prop))).norm.continuousOn.integrableOn_compact
      (isCompact_closedBall c R)
  calc
    _ ≤ ∫ x in B, (2 * R) * ∫ t in I, F (x, t) := by
      apply setIntegral_mono_on hp (hiF.integral_prod_left.const_mul _) measurableSet_closedBall
      intro x hx
      have hh := chord_half_norm_sub_le hf c x y hx hy
      rw [intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
        ← integral_Icc_eq_integral_Ioc] at hh
      exact hh
    _ = (2 * R) * ∫ t in I, ∫ x in B, F (x, t) := by
      rw [integral_const_mul, integral_integral_swap hiF]
    _ ≤ (2 * R) * (2 ^ n * ∫ x in B, G x) := by
      apply mul_le_mul_of_nonneg_left _ hR
      have hh : (∫ t in I, ∫ x in B, F (x, t)) ≤
          ∫ _t in I, (2 : ℝ) ^ n * ∫ x in B, G x := by
        apply setIntegral_mono_on hiF.integral_prod_right continuous_const.integrableOn_Icc measurableSet_Icc
        intro t ht
        exact chord_half_integral_le hG (fun x ↦ norm_nonneg _) c y hy ht
      calc
        _ ≤ _ := hh
        _ ≤ (2 : ℝ) ^ n * ∫ x in B, G x := by
          rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
          have hvol : (volume I).toReal ≤ 1 := by
            norm_num [I, Real.volume_Icc]
          change (volume I).toReal * _ ≤ _
          nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
            (integral_nonneg (μ := volume.restrict B) (fun x ↦ norm_nonneg (fderiv ℝ f x))), measureReal_nonneg (μ := volume) (s := I)]

theorem smooth_ball_poincare {n : ℕ} {f : Euc n → ℝ}
    (hf : ContDiff ℝ 1 f) (c : Euc n) {R : ℝ} (hR : 0 < R) :
    (∫ p, ‖f p.1 - f p.2‖ ∂((volume.restrict (Metric.closedBall c R)).prod
      (volume.restrict (Metric.closedBall c R)))) ≤
      4 * R * volume.real (Metric.closedBall c R) *
        (2 ^ n * ∫ x in Metric.closedBall c R, ‖fderiv ℝ f x‖) := by
  let B := Metric.closedBall c R
  let H : Euc n × Euc n → ℝ := fun p ↦
    ‖f p.1 - f ((1 / 2 : ℝ) • p.1 + (1 / 2 : ℝ) • p.2)‖
  have hHc : Continuous H := (hf.continuous.comp continuous_fst |>.sub
    (hf.continuous.comp (by fun_prop))).norm
  have hHi : Integrable H ((volume.restrict B).prod (volume.restrict B)) := by
    rw [Measure.prod_restrict]
    exact hHc.continuousOn.integrableOn_compact
      ((isCompact_closedBall c R).prod (isCompact_closedBall c R))
  have hDi : Integrable (fun p : Euc n × Euc n ↦ ‖f p.1 - f p.2‖)
      ((volume.restrict B).prod (volume.restrict B)) := by
    rw [Measure.prod_restrict]
    exact ((hf.continuous.comp continuous_fst).sub
      (hf.continuous.comp continuous_snd)).norm.continuousOn.integrableOn_compact
        ((isCompact_closedBall c R).prod (isCompact_closedBall c R))
  have hbound : (∫ p, H p ∂((volume.restrict B).prod (volume.restrict B))) ≤
      volume.real B * ((2 * R) * (2 ^ n * ∫ x in B, ‖fderiv ℝ f x‖)) := by
    rw [integral_prod_symm H hHi]
    calc
      _ ≤ ∫ _y in B, (2 * R) * (2 ^ n * ∫ x in B, ‖fderiv ℝ f x‖) := by
        apply setIntegral_mono_on hHi.integral_prod_right
          (integrableOn_const (isCompact_closedBall c R).measure_ne_top) measurableSet_closedBall
        exact fun y hy ↦ integrated_chord_half_le hf c y hy
      _ = _ := by rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
  have htri : ∀ p : Euc n × Euc n, ‖f p.1 - f p.2‖ ≤ H p + H p.swap := by
    intro p
    simpa only [H, Prod.fst_swap, Prod.snd_swap, add_comm ((1 / 2 : ℝ) • p.2), norm_sub_rev] using
      (norm_sub_le_norm_sub_add_norm_sub (f p.1) (f ((1 / 2 : ℝ) • p.1 + (1 / 2 : ℝ) • p.2)) (f p.2))
  calc
    _ ≤ ∫ p, H p + H p.swap ∂((volume.restrict B).prod (volume.restrict B)) :=
      integral_mono hDi (hHi.add hHi.swap) htri
    _ = 2 * ∫ p, H p ∂((volume.restrict B).prod (volume.restrict B)) := by
      calc
        _ = (∫ p, H p ∂((volume.restrict B).prod (volume.restrict B))) +
            ∫ p, (H ∘ Prod.swap) p ∂((volume.restrict B).prod (volume.restrict B)) :=
          integral_add hHi hHi.swap
        _ = _ := by simp only [Function.comp_def, integral_prod_swap]; ring
    _ ≤ 2 * (volume.real B * ((2 * R) * (2 ^ n * ∫ x in B, ‖fderiv ℝ f x‖))) := by
      apply (mul_le_mul_iff_right₀ hR).mp
      nlinarith [mul_le_mul_of_nonneg_right hbound hR.le]
    _ = _ := by ring

end RPISingularHarnack

end

end OAI
