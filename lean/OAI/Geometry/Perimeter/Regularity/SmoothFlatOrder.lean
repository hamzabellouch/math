import OAI.Geometry.Perimeter.Regularity.TotallyBoundedRangeOfUniformApproximation

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

theorem smooth_flat_order {n : ℕ} {u : Euc n → ℝ}
    (hu : ContDiff ℝ 1 u) {v : Euc n} (hv : ‖v‖ = 1)
    {R : ℝ} (hz : ∀ z ∈ Metric.ball (0 : Euc n) R,
      ∀ w, inner ℝ w v = 0 → fderiv ℝ u z w = 0)
    (hneg : ∀ z ∈ Metric.ball (0 : Euc n) R, fderiv ℝ u z v ≤ 0)
    {x y : Euc n} (hx : x ∈ Metric.ball (0 : Euc n) R)
    (hy : y ∈ Metric.ball (0 : Euc n) R)
    (hxy : inner ℝ x v ≤ inner ℝ y v) : u y ≤ u x := by
  let w := y - x
  let a := inner ℝ w v
  have ha : 0 ≤ a := by dsimp [a, w]; rw [inner_sub_left]; linarith
  have horth : inner ℝ (w - a • v) v = 0 := by
    simp [inner_sub_left, inner_smul_left, hv, a]
  have hdir (z : Euc n) (hzball : z ∈ Metric.ball (0 : Euc n) R) :
      fderiv ℝ u z w ≤ 0 := by
    have heq : w = (w - a • v) + a • v := by abel
    rw [heq, map_add, map_smul, hz z hzball (w - a • v) horth, zero_add,
      smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos ha (hneg z hzball)
  let f : ℝ → ℝ := fun t ↦ u (x + t • w)
  have hd (t : ℝ) : HasDerivAt f (fderiv ℝ u (x + t • w) w) t := by
    simpa only [f, Function.comp_def, id_eq, one_smul] using
      (hu.differentiable one_ne_zero (x + t • w)).hasFDerivAt.comp_hasDerivAt t
        (HasDerivAt.const_add x ((hasDerivAt_id t).smul_const w))
  have hm : AntitoneOn f (Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (hu.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
    · intro t ht
      exact (hd t).hasDerivWithinAt
    · intro t ht
      apply hdir
      exact (convex_ball (0 : Euc n) R).add_smul_sub_mem hx hy (interior_subset ht)
  have he := hm (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) (by norm_num)
  simpa [f, w] using he

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
open scoped Convolution

theorem indicator_convolution_fderiv_eq {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {k : Euc n → ℝ} (hk : ContDiff ℝ ∞ k)
    (hck : HasCompactSupport k) (x v : Euc n) :
    fderiv ℝ (E.indicator (fun _ ↦ (1 : ℝ)) ⋆[lsmul ℝ ℝ, volume] k) x v =
      -(∫ y in E, fderiv ℝ (fun z ↦ k (x - z)) y v) := by
  let χ : Euc n → ℝ := E.indicator (fun _ ↦ 1)
  have hχ : LocallyIntegrable χ volume := indicator_one_locallyIntegrable hE
  rw [(hck.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hχ (hk.of_le (by simp)) x).fderiv]
  rw [convolution_precompR_apply (lsmul ℝ ℝ) hχ (hck.fderiv ℝ)
    (hk.continuous_fderiv (by simp))]
  have hd (y : Euc n) : fderiv ℝ (fun z ↦ k (x - z)) y v =
      -fderiv ℝ k (x - y) v := by
    have h := ((hk.differentiable (by simp) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))).fderiv
    simpa only [Function.comp_def, sub_apply, zero_apply, id_apply,
      zero_sub, ContinuousLinearMap.comp_apply, neg_apply, map_neg] using
      congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L v) h
  simp_rw [hd]
  rw [integral_neg, neg_neg]
  change (∫ t, χ t * fderiv ℝ k (x - t) v) = _
  have heq : (fun t ↦ χ t * fderiv ℝ k (x - t) v) =
      E.indicator (fun t ↦ fderiv ℝ k (x - t) v) := by
    funext t
    by_cases ht : t ∈ E <;> simp [χ, ht]
  rw [heq, integral_indicator hE]

theorem halfspace_of_flat_distribution {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {R : ℝ} (hR : 0 < R) {v : Euc n} (hv : ‖v‖ = 1)
    (hz : ∀ φ : Euc n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball (0 : Euc n) R →
      ∀ w, inner ℝ w v = 0 → (∫ x in E, fderiv ℝ φ x w) = 0)
    (hp : ∀ φ : Euc n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball (0 : Euc n) R → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x in E, fderiv ℝ φ x v) :
    ∃ t ∈ Icc (-R / 2) (R / 2),
      ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Euc n) (R / 2)),
        x ∈ E ↔ inner ℝ x v < t := by
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
  have horder : ∀ᶠ j in atTop, ∀ x ∈ Metric.ball (0 : Euc n) (R / 2),
      ∀ y ∈ Metric.ball (0 : Euc n) (R / 2),
        inner ℝ x v ≤ inner ℝ y v → u j y ≤ u j x := by
    have hsmall : ∀ᶠ j in atTop, (c1Mollifier (n := n) j).rOut < R / 2 :=
      c1Mollifier_radius_tendsto.eventually (gt_mem_nhds (by positivity))
    filter_upwards [hsmall] with j hj
    have hs (x : Euc n) (hx : x ∈ Metric.ball (0 : Euc n) (R / 2)) :
        tsupport (fun z ↦ (c1Mollifier (n := n) j).normed volume (x - z)) ⊆
          Metric.ball (0 : Euc n) R := by
      intro y hy
      have hk := (tsupport_comp_subset_preimage ((c1Mollifier j).normed volume)
        (continuous_const.sub continuous_id)) hy
      rw [(c1Mollifier j).tsupport_normed_eq] at hk
      change x - y ∈ Metric.closedBall (0 : Euc n) (c1Mollifier j).rOut at hk
      have hxy : dist y x ≤ (c1Mollifier (n := n) j).rOut := by
        simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero, norm_sub_rev] using hk
      exact (dist_triangle y x 0).trans_lt (by linarith [Metric.mem_ball.mp hx])
    have hzero : ∀ z ∈ Metric.ball (0 : Euc n) (R / 2),
        ∀ w, inner ℝ w v = 0 → fderiv ℝ (u j) z w = 0 := by
      intro z hzball w hw
      rw [hu_eq j, indicator_convolution_fderiv_eq hE
        (c1Mollifier j).contDiff_normed (c1Mollifier j).hasCompactSupport_normed]
      apply neg_eq_zero.mpr
      exact hz _ ((c1Mollifier j).contDiff_normed.comp (contDiff_const.sub contDiff_id))
        ((c1Mollifier j).hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft z))
        (hs z hzball) w hw
    have hnonpos : ∀ z ∈ Metric.ball (0 : Euc n) (R / 2), fderiv ℝ (u j) z v ≤ 0 := by
      intro z hzball
      rw [hu_eq j, indicator_convolution_fderiv_eq hE
        (c1Mollifier j).contDiff_normed (c1Mollifier j).hasCompactSupport_normed]
      apply neg_nonpos.mpr
      exact hp _ ((c1Mollifier j).contDiff_normed.comp (contDiff_const.sub contDiff_id))
        ((c1Mollifier j).hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft z))
        (hs z hzball) (fun y ↦ (c1Mollifier j).nonneg_normed (z - y))
    intro x hx y hy hxy
    exact smooth_flat_order ((hu j).of_le (by simp)) hv hzero hnonpos hx hy hxy
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun j ↦ u j x) atTop (𝓝 (χ x)) := by
    apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      c1Mollifier_radius_tendsto (K := 2) _ hχ
    apply Eventually.of_forall
    intro j
    dsimp [c1Mollifier]
    linarith
  let S := {x | Tendsto (fun j ↦ u j x) atTop (𝓝 (χ x))}
  have hS : ∀ᵐ x ∂volume, x ∈ S := hlim
  have hd : ∀ x ∈ S ∩ Metric.ball (0 : Euc n) (R / 2),
      ∀ y ∈ S ∩ Metric.ball (0 : Euc n) (R / 2),
        inner ℝ x v < inner ℝ y v → y ∈ E → x ∈ E := by
    intro x hx y hy hxy hyE
    have hle : χ y ≤ χ x := le_of_tendsto_of_tendsto hy.1 hx.1
      (horder.mono fun j hj ↦ hj x hx.2 y hy.2 hxy.le)
    by_contra hxE
    norm_num [χ, hxE, hyE] at hle
  simpa only [neg_div] using ordered_indicator_halfspace E S hS hv (by positivity : 0 < R / 2) hd

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

theorem halfspace_threshold_eq_zero {n : ℕ} {E : Set (Euc n)}
    {R : ℝ} (hR : 0 < R) {v : Euc n} (hv : ‖v‖ = 1) {t : ℝ}
    (hhalf : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Euc n) R),
      x ∈ E ↔ inner ℝ x v < t)
    (hphase : ∀ s : ℝ, 0 < s → s ≤ R →
      0 < volume (E ∩ Metric.ball (0 : Euc n) s) ∧
      0 < volume (Eᶜ ∩ Metric.ball (0 : Euc n) s)) : t = 0 := by
  have ha := (ae_restrict_iff' measurableSet_ball).mp hhalf
  have hinner (x : Euc n) {s : ℝ} (hx : x ∈ Metric.ball (0 : Euc n) s) :
      |inner ℝ x v| < s := by
    apply (abs_real_inner_le_norm x v).trans_lt
    simpa only [hv, mul_one, Metric.mem_ball, dist_zero_right] using hx
  rcases lt_trichotomy t 0 with ht | ht | ht
  · let s := min R (-t) / 2
    have hs : 0 < s := by
      dsimp [s]
      exact div_pos (lt_min hR (neg_pos.mpr ht)) (by norm_num)
    have hsR : s ≤ R := by dsimp [s]; linarith [min_le_left R (-t)]
    have hst : s < -t := by dsimp [s]; linarith [min_le_right R (-t), lt_min hR (neg_pos.mpr ht)]
    have hno : ∀ᵐ x ∂volume, x ∉ E ∩ Metric.ball (0 : Euc n) s := by
      filter_upwards [ha] with x hx
      intro hxin
      have hxR := Metric.ball_subset_ball hsR hxin.2
      have hxt := (hx hxR).mp hxin.1
      have hb := (abs_lt.mp (hinner x hxin.2)).1
      linarith
    have hz : volume (E ∩ Metric.ball (0 : Euc n) s) = 0 := by
      simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hno
    exact False.elim (ne_of_gt (hphase s hs hsR).1 hz)
  · exact ht
  · let s := min R t / 2
    have hs : 0 < s := by dsimp [s]; positivity
    have hsR : s ≤ R := by dsimp [s]; linarith [min_le_left R t]
    have hst : s < t := by dsimp [s]; linarith [min_le_right R t, lt_min hR ht]
    have hno : ∀ᵐ x ∂volume, x ∉ Eᶜ ∩ Metric.ball (0 : Euc n) s := by
      filter_upwards [ha] with x hx
      intro hxin
      have hxR := Metric.ball_subset_ball hsR hxin.2
      have hxt : inner ℝ x v < t := (abs_lt.mp (hinner x hxin.2)).2.trans hst
      exact hxin.1 ((hx hxR).mpr hxt)
    have hz : volume (Eᶜ ∩ Metric.ball (0 : Euc n) s) = 0 := by
      simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hno
    exact False.elim (ne_of_gt (hphase s hs hsR).2 hz)

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

def blownUpSet {n : ℕ} (E : Set (Euc n)) (c : Euc n) (r : ℝ) : Set (Euc n) :=
  (fun z ↦ c + r • z) ⁻¹' E

theorem measurableSet_blownUpSet {n : ℕ} {E : Set (Euc n)} (hE : MeasurableSet E)
    (c : Euc n) (r : ℝ) : MeasurableSet (blownUpSet E c r) :=
  hE.preimage (by fun_prop)

theorem integral_blownUpSet {n : ℕ} {E : Set (Euc n)} (hE : MeasurableSet E)
    (g : Euc n → ℝ) (c : Euc n) {r : ℝ} (hr : 0 < r) :
    (∫ z in blownUpSet E c r, g (c + r • z)) = (r ^ n)⁻¹ * ∫ y in E, g y := by
  have hc := Measure.integral_comp_smul_of_nonneg (volume : Measure (Euc n))
    (fun y ↦ E.indicator g (c + y)) r (hR := hr.le)
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
    integral_add_left_eq_self, integral_indicator hE] at hc
  rw [← hc, ← integral_indicator (measurableSet_blownUpSet hE c r)]
  apply integral_congr_ae
  exact ae_of_all _ fun z ↦ by
    by_cases hz : c + r • z ∈ E <;> simp [blownUpSet, hz]

theorem divergence_comp_blowdown {n : ℕ} {V : Euc n → Euc n}
    (hV : Differentiable ℝ V) (c : Euc n) (r : ℝ) (y : Euc n) :
    divergence (fun z ↦ V (r⁻¹ • (z - c))) y =
      r⁻¹ * divergence V (r⁻¹ • (y - c)) := by
  have hd := ((hV _).hasFDerivAt.comp y
    (((hasFDerivAt_id y).sub_const c).const_smul r⁻¹)).fderiv
  simp only [Function.comp_def, id_eq, Pi.smul_apply] at hd
  simp only [divergence, hd, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_smul,
    inner_smul_right, ← Finset.mul_sum]

theorem perimeter_blownUpSet_le {n : ℕ} {E : Set (Euc n)} (hE : MeasurableSet E)
    (c : Euc n) {r R : ℝ} (hr : 0 < r)
    (hP : perimeter E (Metric.ball c (r * R)) ≠ ⊤) :
    perimeter (blownUpSet E c r) (Metric.ball (0 : Euc n) R) ≤
      ENNReal.ofReal (r * (r ^ n)⁻¹ * (perimeter E (Metric.ball c (r * R))).toReal) := by
  rw [perimeter_eq_iSup_tests]
  refine iSup_le fun V ↦ iSup_le fun hV ↦ ?_
  let W : Euc n → Euc n := fun y ↦ V (r⁻¹ • (y - c))
  have hW : PerimeterAdmissible (Metric.ball c (r * R)) W := by
    refine ⟨hV.1.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹), ?_, ?_, ?_⟩
    · exact hV.2.1.comp_homeomorph
        ((Homeomorph.subRight c).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')))
    · intro y hy
      have hys := tsupport_comp_subset_preimage V
        ((continuous_id.sub continuous_const).const_smul r⁻¹) hy
      have hyb := hV.2.2.1 hys
      change r⁻¹ • (y - c) ∈ Metric.ball (0 : Euc n) R at hyb
      simp only [Metric.mem_ball, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hr.le)] at hyb
      change dist y c < r * R
      rw [dist_eq_norm]
      have he : r * (r⁻¹ * ‖y - c‖) = ‖y - c‖ := by field_simp
      linarith [mul_lt_mul_of_pos_left hyb hr]
    · exact fun y ↦ hV.2.2.2 _
  have he (z : Euc n) : divergence W (c + r • z) = r⁻¹ * divergence V z := by
    dsimp [W]
    rw [divergence_comp_blowdown (hV.1.differentiable (by simp))]
    simp [inv_smul_smul₀ hr.ne']
  have hint := integral_blownUpSet hE (divergence W) c hr
  simp_rw [he] at hint
  rw [integral_const_mul] at hint
  have hint' : (∫ z in blownUpSet E c r, divergence V z) =
      (r * (r ^ n)⁻¹) * ∫ y in E, divergence W y := by
    have heq := congrArg (fun a : ℝ ↦ r * a) hint
    have hrinv : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
    simpa only [← mul_assoc, hrinv, one_mul] using heq
  rw [hint']
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (integral_divergence_le_perimeter_real E _ hP hW)
    (by positivity)

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

theorem exists_fixed_annular_bv_cut {n : ℕ} :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ E : Set (Euc n), MeasurableSet E →
      perimeter E (Metric.ball (0 : Euc n) 4) ≠ ⊤ →
      ∃ r ∈ Ico (2 : ℝ) 3,
        perimeter (E ∩ Metric.closedBall (0 : Euc n) r) univ ≤
          perimeter E (Metric.ball (0 : Euc n) 4) + D := by
  obtain ⟨L, hL, hbound⟩ := exists_smoothTransition_deriv_bound
  let D : ℝ := volume.real (Metric.closedBall (0 : Euc n) 3) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨ENNReal.ofReal (8 * L * D), ENNReal.ofReal_ne_top, ?_⟩
  intro E hE hP
  have hvol : volume.real (E ∩ Metric.closedBall (0 : Euc n) 3) < D * (3 - 2) := by
    have hm := measureReal_mono (μ := (volume : Measure (Euc n)))
      (s₁ := E ∩ Metric.closedBall (0 : Euc n) 3) inter_subset_right
      (isCompact_closedBall (0 : Euc n) 3).measure_ne_top
    dsimp [D]
    linarith
  obtain ⟨r, hr, hc⟩ := exists_controlled_cut_radius E (0 : Euc n)
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3) hvol
  refine ⟨r, hr, ?_⟩
  have hcut := controlled_radius_perimeter_cut hE (0 : Euc n)
    (by linarith [hr.1] : 0 < r) hr.2
    (Metric.closedBall_subset_ball (by norm_num : (3 : ℝ) < 4))
    hc hD.le hL hbound hP
  exact (le_add_right le_rfl).trans hcut

theorem exists_local_indicator_L1_subsequence {n : ℕ} (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (E : ℕ → Set (Euc n)) (hE : ∀ i, MeasurableSet (E i))
    (hP : ∀ i, perimeter (E i) (Metric.ball (0 : Euc n) 4) ≤ C) :
    ∃ F : Set (Euc n), MeasurableSet F ∧ F ⊆ Metric.closedBall (0 : Euc n) 3 ∧
      ∃ A : ℕ → Set (Euc n), (∀ i, MeasurableSet (A i)) ∧
        (∀ i, A i ∩ Metric.ball (0 : Euc n) 2 = E i ∩ Metric.ball (0 : Euc n) 2) ∧
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
          Tendsto (fun i ↦ ∫⁻ x, ‖(A (σ i)).indicator (fun _ ↦ (1 : ℝ)) x -
            F.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ) atTop (𝓝 0) := by
  obtain ⟨D, hD, hcut⟩ := exists_fixed_annular_bv_cut (n := n)
  choose r hr hpr using fun i ↦ hcut (E i) (hE i) (ne_top_of_le_ne_top hC (hP i))
  let A : ℕ → Set (Euc n) := fun i ↦ E i ∩ Metric.closedBall 0 (r i)
  have hA : ∀ i, MeasurableSet (A i) := fun i ↦ (hE i).inter measurableSet_closedBall
  have hAK : ∀ i, A i ⊆ Metric.closedBall (0 : Euc n) 3 := fun i ↦
    inter_subset_right.trans (Metric.closedBall_subset_closedBall (hr i).2.le)
  have hpA : ∀ i, perimeter (A i) univ ≤ C + D := fun i ↦
    (hpr i).trans (add_le_add (hP i) le_rfl)
  obtain ⟨F, hF, hFK, σ, hσ, ht⟩ := exists_indicator_L1_subsequence
    (Metric.closedBall (0 : Euc n) 3) (isCompact_closedBall _ _) (C + D)
      (ENNReal.add_ne_top.mpr ⟨hC, hD⟩) A hA hAK hpA
  refine ⟨F, hF, hFK, A, hA, ?_, σ, hσ, ht⟩
  intro i
  ext x
  constructor
  · exact fun hx ↦ ⟨hx.1.1, hx.2⟩
  · intro hx
    exact ⟨⟨hx.1, (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (hr i).1)) hx.2⟩, hx.2⟩

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

theorem exists_blownUpSet_perimeter_bound {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ E : Set (Euc n), IsLocallyPerimeterMinimizing E →
      ∀ c (r : ℝ), 0 < r →
        perimeter (blownUpSet E c r) (Metric.ball (0 : Euc n) 4) ≤ C := by
  obtain ⟨C, hC, hgrowth⟩ := exists_locallyMinimizing_perimeter_growth_constant n hn
  refine ⟨ENNReal.ofReal (C * 4 ^ (n - 1)), ENNReal.ofReal_ne_top, ?_⟩
  intro E hmin c r hr
  have hb := hgrowth E hmin c (r * 4) (by positivity)
  have hfin : perimeter E (Metric.ball c (r * 4)) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hreal : (perimeter E (Metric.ball c (r * 4))).toReal ≤ C * (r * 4) ^ (n - 1) := by
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ C * (r * 4) ^ (n - 1))] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  apply (perimeter_blownUpSet_le hmin.1 c hr hfin).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    r * (r ^ n)⁻¹ * (perimeter E (Metric.ball c (r * 4))).toReal ≤
        r * (r ^ n)⁻¹ * (C * (r * 4) ^ (n - 1)) :=
      mul_le_mul_of_nonneg_left hreal (by positivity)
    _ = C * 4 ^ (n - 1) := by
      have hn' : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
      have he : r ^ n = r * r ^ (n - 1) := by conv_lhs => rw [hn']; rw [pow_succ'];
      rw [he, mul_pow]
      field_simp

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

theorem divergence_scalar_direction {n : ℕ} {φ : Euc n → ℝ}
    (hφ : Differentiable ℝ φ) (w : Euc n) :
    divergence (fun y ↦ φ y • w) = fun y ↦ fderiv ℝ φ y w := by
  funext y
  rw [divergence_smul hφ (differentiable_const w)]
  simp only [divergence, fderiv_fun_const, Pi.zero_apply, zero_apply,
    inner_zero_right, Finset.sum_const_zero, mul_zero, zero_add, inner_gradient_left]

theorem integral_fderiv_blownUpSet {n : ℕ} {E : Set (Euc n)} (hE : MeasurableSet E)
    {φ : Euc n → ℝ} (hφ : Differentiable ℝ φ) (c w : Euc n) {r : ℝ} (hr : 0 < r) :
    (∫ z in blownUpSet E c r, fderiv ℝ φ z w) =
      (r * (r ^ n)⁻¹) * ∫ y in E, fderiv ℝ (fun z ↦ φ (r⁻¹ • (z - c))) y w := by
  have hd (y : Euc n) : fderiv ℝ (fun z ↦ φ (r⁻¹ • (z - c))) y w =
      r⁻¹ * fderiv ℝ φ (r⁻¹ • (y - c)) w := by
    have h := ((hφ _).hasFDerivAt.comp y
      (((hasFDerivAt_id y).sub_const c).const_smul r⁻¹)).fderiv
    simp only [Function.comp_def, id_eq, Pi.smul_apply] at h
    rw [h, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  have he (z : Euc n) : fderiv ℝ (fun y ↦ φ (r⁻¹ • (y - c))) (c + r • z) w =
      r⁻¹ * fderiv ℝ φ z w := by rw [hd]; simp [inv_smul_smul₀ hr.ne']
  have hint := integral_blownUpSet hE
    (fun y ↦ fderiv ℝ (fun z ↦ φ (r⁻¹ • (z - c))) y w) c hr
  simp_rw [he] at hint
  rw [integral_const_mul] at hint
  have heq := congrArg (fun a : ℝ ↦ r * a) hint
  simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] using heq

theorem integral_fderiv_blownUpSet_polar {n : ℕ} {E U : Set (Euc n)}
    (hE : MeasurableSet E) (μ : Measure (Euc n)) (G : Euc n → Euc n)
    (hrep : ∀ V : Euc n → Euc n, ContDiff ℝ ∞ V → HasCompactSupport V →
      tsupport V ⊆ U → (∫ y in E, divergence V y) = ∫ y, inner ℝ (G y) (V y) ∂μ)
    {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (c w : Euc n) {r : ℝ} (hr : 0 < r)
    (hs : tsupport (fun y ↦ φ (r⁻¹ • (y - c))) ⊆ U) :
    (∫ z in blownUpSet E c r, fderiv ℝ φ z w) =
      (r * (r ^ n)⁻¹) * ∫ y, φ (r⁻¹ • (y - c)) * inner ℝ (G y) w ∂μ := by
  let ψ : Euc n → ℝ := fun y ↦ φ (r⁻¹ • (y - c))
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)
  have hcψ : HasCompactSupport ψ := hcφ.comp_homeomorph
    ((Homeomorph.subRight c).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')))
  rw [integral_fderiv_blownUpSet hE (hφ.differentiable (by simp)) c w hr]
  have he := hrep (fun y ↦ ψ y • w) (hψ.smul contDiff_const) hcψ.smul_right
    ((tsupport_smul_subset_left ψ (fun _ ↦ w)).trans hs)
  rw [divergence_scalar_direction (hψ.differentiable (by simp))] at he
  simp only [inner_smul_right] at he
  rw [he]

theorem polar_test_oscillation_le {n : ℕ} (μ : Measure (Euc n)) [IsFiniteMeasure μ]
    {G : Euc n → Euc n} (hG : Integrable G μ) (v w : Euc n)
    {ψ : Euc n → ℝ} (hψ : Continuous ψ) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ y, ‖ψ y‖ ≤ M) (B : Set (Euc n)) (hB : MeasurableSet B)
    (hs : ∀ y ∉ B, ψ y = 0) :
    |(∫ y, ψ y * inner ℝ (G y) w ∂μ) -
      (∫ y, ψ y * inner ℝ v w ∂μ)| ≤
      M * ‖w‖ * ∫ y in B, ‖G y - v‖ ∂μ := by
  have hiψ : Integrable ψ μ := Integrable.of_bound hψ.aestronglyMeasurable M (ae_of_all _ hb)
  have hib : Integrable (fun y ↦ ψ y * inner ℝ (G y - v) w) μ := by
    apply (hG.sub (integrable_const v)).norm.mul_const (M * ‖w‖) |>.mono'
    · exact hψ.aestronglyMeasurable.mul
        ((hG.aestronglyMeasurable.sub stronglyMeasurable_const.aestronglyMeasurable).inner
          stronglyMeasurable_const.aestronglyMeasurable)
    · filter_upwards [] with y
      rw [norm_mul, Real.norm_eq_abs]
      have hin := abs_real_inner_le_norm (G y - v) w
      calc
        ‖ψ y‖ * |inner ℝ (G y - v) w| ≤ M * (‖G y - v‖ * ‖w‖) :=
          mul_le_mul (hb y) hin (abs_nonneg _) hM
        _ = ‖G y - v‖ * (M * ‖w‖) := by ring
  have hiG : Integrable (fun y ↦ ψ y * inner ℝ (G y) w) μ := by
    have he : (fun y ↦ ψ y * inner ℝ (G y) w) =
        (fun y ↦ ψ y * inner ℝ (G y - v) w) + (fun y ↦ ψ y * inner ℝ v w) := by
      funext y
      simp only [Pi.add_apply, inner_sub_left]
      ring
    rw [he]
    exact hib.add (hiψ.mul_const _)
  have heq : (∫ y, ψ y * inner ℝ (G y) w ∂μ) - (∫ y, ψ y * inner ℝ v w ∂μ) =
      ∫ y in B, ψ y * inner ℝ (G y - v) w ∂μ := by
    rw [← integral_sub hiG (hiψ.mul_const _)]
    have he : (fun y ↦ ψ y * inner ℝ (G y) w - ψ y * inner ℝ v w) =
        fun y ↦ ψ y * inner ℝ (G y - v) w := by funext y; rw [inner_sub_left, mul_sub]
    rw [he]
    rw [← integral_indicator hB]
    apply integral_congr_ae
    exact ae_of_all _ fun point ↦ by
      by_cases hpoint : point ∈ B
      · rw [indicator_of_mem hpoint]
      · simp only [indicator_of_notMem hpoint, hs point hpoint, zero_mul]
  rw [heq]
  calc
    _ ≤ ∫ y in B, |ψ y * inner ℝ (G y - v) w| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ y in B, M * ‖w‖ * ‖G y - v‖ ∂μ := by
      apply integral_mono hib.integrableOn.norm
        (((hG.sub (integrable_const v)).norm.const_mul (M * ‖w‖)).integrableOn)
      intro y
      change ‖ψ y * inner ℝ (G y - v) w‖ ≤ M * ‖w‖ * ‖G y - v‖
      rw [norm_mul, Real.norm_eq_abs (inner ℝ (G y - v) w)]
      calc
        _ ≤ M * (‖G y - v‖ * ‖w‖) :=
          mul_le_mul (hb y) (abs_real_inner_le_norm _ _) (abs_nonneg _) hM
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

end RPISingularHarnack

end

end OAI
