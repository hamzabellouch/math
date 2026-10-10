import OAI.Geometry.Perimeter.Regularity.IntegralDivergenceEqZeroOfPerimeterEqZero

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack
open RPI.Boundary
open ContinuousLinearMap
open scoped Convolution

theorem indicator_convolution_variation_local_le {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (U W : Set (Euc n)) (hP : perimeter E W ≠ ⊤)
    {k : Euc n → ℝ} (hkc : Continuous k) (hk : Integrable k volume)
    (hk0 : ∀ x, 0 ≤ k x) (hk1 : ∫ x, k x = 1)
    (hshift : ∀ t ∈ tsupport k, ∀ y, y + t ∈ U → y ∈ W)
    {V : Euc n → Euc n} (hV : PerimeterAdmissible U V) :
    (∫ x, (k ⋆[lsmul ℝ ℝ, volume] E.indicator (fun _ ↦ (1 : ℝ))) x * divergence V x) ≤
      (perimeter E W).toReal := by
  let χ : Euc n → ℝ := E.indicator (fun _ ↦ 1)
  have hmχ : Measurable χ := measurable_const.indicator hE
  have hbχ : ∀ x, ‖χ x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ E <;> simp [χ, hx]
  have hd := integrable_divergence hV.1 hV.2.1
  let F : Euc n × Euc n → ℝ := fun p ↦ k p.1 * χ (p.2 - p.1) * divergence V p.2
  have hFi : Integrable F (volume.prod volume) := by
    apply (hk.norm.mul_prod hd.norm).mono'
    · exact ((hkc.measurable.comp measurable_fst).mul
        (hmχ.comp (measurable_snd.sub measurable_fst))).mul
        ((continuous_divergence hV.1).measurable.comp measurable_snd) |>.aestronglyMeasurable
    · apply ae_of_all
      intro p
      simp only [F, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (by nlinarith [hbχ (p.2 - p.1), norm_nonneg (k p.1)]) (norm_nonneg _)
  have hinner : ∀ t, (∫ x, F (t, x)) = k t * (∫ y in E, divergence V (y + t)) := by
    intro t
    simp only [F, mul_assoc, integral_const_mul]
    congr 1
    calc
      (∫ x, χ (x - t) * divergence V x) =
          ∫ y, χ y * divergence V (y + t) := by
        simpa only [add_sub_cancel_right] using
          (integral_add_right_eq_self (fun x ↦ χ (x - t) * divergence V x) t).symm
      _ = ∫ y in E, divergence V (y + t) := by
        rw [← integral_indicator hE]
        apply integral_congr_ae
        apply ae_of_all
        intro y
        by_cases hy : y ∈ E <;> simp [χ, hy]
  have hInt : Integrable (fun t ↦ k t * (∫ y in E, divergence V (y + t))) volume := by
    simpa only [hinner] using hFi.integral_prod_left
  have heq : (∫ x, (k ⋆[lsmul ℝ ℝ, volume] χ) x * divergence V x) =
      ∫ t, k t * (∫ y in E, divergence V (y + t)) := by
    calc
      _ = ∫ x, ∫ t, F (t, x) := by
        apply integral_congr_ae
        apply ae_of_all
        intro x
        simp only [convolution_def, lsmul_apply, smul_eq_mul, F, integral_mul_const]
      _ = ∫ t, ∫ x, F (t, x) := integral_integral_swap hFi.swap
      _ = _ := by simp only [hinner]
  have hbound : ∀ t, k t * (∫ y in E, divergence V (y + t)) ≤ k t * (perimeter E W).toReal := by
    intro t
    by_cases ht : k t = 0
    · simp only [ht, zero_mul, le_refl]
    have htk : t ∈ tsupport k := subset_closure ht
    let Vt : Euc n → Euc n := fun y ↦ V (y + t)
    have hVs : tsupport Vt ⊆ W := by
      intro y hy
      apply hshift t htk y
      exact hV.2.2.1 ((tsupport_comp_subset_preimage V (continuous_id.add continuous_const)) hy)
    have hVt : PerimeterAdmissible W Vt := ⟨hV.1.comp (contDiff_id.add contDiff_const),
      hV.2.1.comp_homeomorph (Homeomorph.addRight t), hVs, fun y ↦ hV.2.2.2 _⟩
    have hh : (∫ y in E, divergence V (y + t)) ≤ (perimeter E W).toReal := by
      simpa only [Vt, divergence_comp_add_right (hV.1.differentiable (by simp))] using
        integral_divergence_le_perimeter_real E W hP hVt
    exact mul_le_mul_of_nonneg_left hh (hk0 t)
  rw [heq]
  calc
    (∫ t, k t * (∫ y in E, divergence V (y + t))) ≤
        ∫ t, k t * (perimeter E W).toReal := by
      exact integral_mono hInt (hk.mul_const _) hbound
    _ = (perimeter E W).toReal := by rw [integral_mul_const, hk1, one_mul]

theorem scalar_compact_integration_parts {n : ℕ} {u v : Euc n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hcv : HasCompactSupport v)
    (a : Euc n) :
    Integrable (fun x ↦ u x * fderiv ℝ v x a) volume ∧
    Integrable (fun x ↦ fderiv ℝ u x a * v x) volume ∧
    (∫ x, u x * fderiv ℝ v x a) = -(∫ x, fderiv ℝ u x a * v x) := by
  have hdu : Continuous (fun x ↦ fderiv ℝ u x a) :=
    (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdv : Continuous (fun x ↦ fderiv ℝ v x a) :=
    (hv.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdv : HasCompactSupport (fun x ↦ fderiv ℝ v x a) :=
    hcv.fderiv_apply ℝ a
  have h1 : Integrable (fun x ↦ u x * fderiv ℝ v x a) volume :=
    (hu.continuous.mul hdv).integrable_of_hasCompactSupport hcdv.mul_left
  have h2 : Integrable (fun x ↦ fderiv ℝ u x a * v x) volume :=
    (hdu.mul hv.continuous).integrable_of_hasCompactSupport hcv.mul_left
  refine ⟨h1, h2, ?_⟩
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h2 h1
    ((hu.continuous.mul hv.continuous).integrable_of_hasCompactSupport hcv.mul_left)
    (fun x _ ↦ hu.differentiable (by simp) x)
    (fun x _ ↦ hv.differentiable (by simp) x)

theorem integral_mul_divergence_eq_neg_inner_gradient_local {n : ℕ} {u : Euc n → ℝ}
    {V : Euc n → Euc n} (hu : ContDiff ℝ ∞ u)
    (hV : ContDiff ℝ ∞ V) (hcV : HasCompactSupport V) :
    (∫ x, u x * divergence V x) = - ∫ x, inner ℝ (gradient u x) (V x) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let v : Fin n → Euc n → ℝ := fun i x ↦ inner ℝ (b i) (V x)
  have hv : ∀ i, ContDiff ℝ ∞ (v i) := fun i ↦ (innerSL ℝ (b i)).contDiff.comp hV
  have hcv : ∀ i, HasCompactSupport (v i) := fun i ↦ hcV.comp_left (by simp)
  have hdv : ∀ i x, fderiv ℝ (v i) x (b i) =
      inner ℝ (b i) (fderiv ℝ V x (b i)) := by
    intro i x
    have h := ((innerSL ℝ (b i)).hasFDerivAt.comp x
      (hV.differentiable (by simp) x).hasFDerivAt).fderiv
    exact congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L (b i)) h
  have hp := fun i ↦ scalar_compact_integration_parts hu (hv i) (hcv i) (b i)
  have hInt1 := fun i ↦ (hp i).2.1
  have hInt2 := fun i ↦ (hp i).1
  have hparts := fun i ↦ (hp i).2.2
  calc
    (∫ x, u x * divergence V x) = ∫ x, ∑ i, u x * fderiv ℝ (v i) x (b i) := by
      congr 1
      funext x
      simp only [divergence, hdv, Finset.mul_sum, b]
    _ = ∑ i, ∫ x, u x * fderiv ℝ (v i) x (b i) := integral_finsetSum _ (fun i _ ↦ hInt2 i)
    _ = -(∑ i, ∫ x, fderiv ℝ u x (b i) * v i x) := by simp only [hparts, Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ i, fderiv ℝ u x (b i) * v i x) := by
      rw [integral_finsetSum _ (fun i _ ↦ hInt1 i)]
    _ = -(∫ x, inner ℝ (gradient u x) (V x)) := by
      congr 1
      apply integral_congr_ae
      apply ae_of_all
      intro x
      simp only [← inner_gradient_left, v]
      exact b.sum_inner_mul_inner _ _

theorem integral_weighted_norm_gradient_le_of_test_bound {n : ℕ} {u : Euc n → ℝ}
    (hu : ContDiff ℝ ∞ u) {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (U : Set (Euc n)) (hsφ : tsupport φ ⊆ U) {P : ℝ}
    (hbound : ∀ V : Euc n → Euc n, PerimeterAdmissible U V →
      (∫ x, u x * divergence V x) ≤ P) :
    (∫ x, φ x * ‖gradient u x‖) ≤ P := by
  let ε : ℕ → ℝ := fun j ↦ 1 / (j + 1 : ℝ)
  have hε : ∀ j, 0 < ε j := by intro j; dsimp [ε]; positivity
  let f : ℕ → Euc n → ℝ := fun j x ↦
    ‖gradient u x‖ ^ 2 / Real.sqrt (ε j ^ 2 + ‖gradient u x‖ ^ 2)
  have hg := (gradient_contDiff hu).continuous
  have hgi : Integrable (fun x ↦ φ x * ‖gradient u x‖) volume :=
    (hφ.continuous.mul hg.norm).integrable_of_hasCompactSupport hcφ.mul_right
  have hf0 : ∀ j x, 0 ≤ f j x := by intro j x; exact div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hfle : ∀ j x, f j x ≤ ‖gradient u x‖ := by
    intro j x
    have hp : 0 < ε j ^ 2 + ‖gradient u x‖ ^ 2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_pos (hε j)) (sq_nonneg _)
    have hs : ‖gradient u x‖ ≤ Real.sqrt (ε j ^ 2 + ‖gradient u x‖ ^ 2) := by
      rw [Real.le_sqrt (norm_nonneg _) hp.le]
      nlinarith [sq_nonneg (ε j)]
    exact (div_le_iff₀ (Real.sqrt_pos.2 hp)).2 (by nlinarith [norm_nonneg (gradient u x)])
  have hfcont : ∀ j, Continuous (f j) := by
    intro j
    exact (hg.norm.pow 2).div ((continuous_const.add (hg.norm.pow 2)).sqrt)
      (fun x ↦ (Real.sqrt_pos.2
        (add_pos_of_pos_of_nonneg (sq_pos_of_pos (hε j)) (sq_nonneg _))).ne')
  have hflim : ∀ x, Tendsto (fun j ↦ f j x) atTop (𝓝 ‖gradient u x‖) := by
    intro x
    have hlim : Tendsto ε atTop (𝓝 0) := by
      simpa only [ε, Nat.cast_add, Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat
    by_cases hx : ‖gradient u x‖ = 0
    · simp [f, hx]
    · have hden := ((hlim.pow 2).add_const (‖gradient u x‖ ^ 2)).sqrt
      have hden' : Tendsto (fun j ↦ Real.sqrt (ε j ^ 2 + ‖gradient u x‖ ^ 2))
          atTop (𝓝 ‖gradient u x‖) := by
        simpa [Real.sqrt_sq (norm_nonneg _)] using hden
      have hh := (tendsto_const_nhds (x := ‖gradient u x‖ ^ 2)).div hden' hx
      have heq : ‖gradient u x‖ ^ 2 / ‖gradient u x‖ = ‖gradient u x‖ := by
        rw [pow_two, mul_div_cancel_right₀ _ hx]
      change Tendsto (fun j ↦ ‖gradient u x‖ ^ 2 / Real.sqrt (ε j ^ 2 + ‖gradient u x‖ ^ 2))
        atTop (𝓝 (‖gradient u x‖ ^ 2 / ‖gradient u x‖)) at hh
      rw [heq] at hh
      exact hh
  have hlim : Tendsto (fun j ↦ ∫ x, φ x * f j x) atTop
      (𝓝 (∫ x, φ x * ‖gradient u x‖)) :=
    tendsto_integral_of_dominated_convergence (fun x ↦ φ x * ‖gradient u x‖)
      (fun j ↦ (hφ.continuous.mul (hfcont j)).aestronglyMeasurable)
      hgi (fun j ↦ ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hφ0 x) (hf0 j x))]
        exact mul_le_mul_of_nonneg_left (hfle j x) (hφ0 x))
      (ae_of_all _ fun x ↦ (hflim x).const_mul (φ x))
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro j
  let V : Euc n → Euc n := fun x ↦ φ x • gradientDualTest u (ε j) x
  have hV : PerimeterAdmissible U V := by
    refine ⟨hφ.smul (gradientDualTest_contDiff hu (hε j)), hcφ.smul_right,
      (tsupport_smul_subset_left φ _).trans hsφ, ?_⟩
    intro x
    simp only [V, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφ0 x)]
    calc
      φ x * ‖gradientDualTest u (ε j) x‖ ≤ φ x * 1 :=
        mul_le_mul_of_nonneg_left (gradientDualTest_norm_le u (hε j) x) (hφ0 x)
      _ ≤ 1 := by simpa only [mul_one] using hφ1 x
  have heq : (∫ x, u x * divergence V x) = ∫ x, φ x * f j x := by
    rw [integral_mul_divergence_eq_neg_inner_gradient_local hu hV.1 hV.2.1, ← integral_neg]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    simp only [V, gradientDualTest, inner_smul_right, real_inner_self_eq_norm_sq,
      f, neg_mul, mul_neg, neg_neg, div_eq_mul_inv]
    ring
  rw [← heq]
  exact hbound V hV

theorem c1Mollify_indicator_local_gradient_le {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (c : Euc n) {R : ℝ} (hR : 0 < R)
    (hP : perimeter E (Metric.ball c (4 * R)) ≠ ⊤) (j : ℕ)
    (hj : (c1Mollifier (n := n) j).rOut < R) :
    (∫ x in Metric.closedBall c R,
      ‖fderiv ℝ (c1Mollify (E.indicator (fun _ ↦ (1 : ℝ))) j) x‖) ≤
      (perimeter E (Metric.ball c (4 * R))).toReal := by
  let χ : Euc n → ℝ := E.indicator (fun _ ↦ 1)
  let u := c1Mollify χ j
  let φ : ContDiffBump c := ⟨R, 2 * R, hR, by linarith⟩
  have hu : ContDiff ℝ ∞ u :=
    (c1Mollifier j).hasCompactSupport_normed.contDiff_convolution_left _
      (c1Mollifier j).contDiff_normed (indicator_one_locallyIntegrable hE)
  have hsφ : tsupport φ ⊆ Metric.ball c (3 * R) := by
    rw [φ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [φ]; linarith)
  have hgrad : (∫ x, φ x * ‖gradient u x‖) ≤
      (perimeter E (Metric.ball c (4 * R))).toReal := by
    apply integral_weighted_norm_gradient_le_of_test_bound hu φ.contDiff
      φ.hasCompactSupport (fun _ ↦ φ.nonneg) (fun _ ↦ φ.le_one) (Metric.ball c (3 * R)) hsφ
    intro V hV
    apply indicator_convolution_variation_local_le hE
      (Metric.ball c (3 * R)) (Metric.ball c (4 * R)) hP
      (c1Mollifier j).continuous_normed
      ((c1Mollifier j).continuous_normed.integrable_of_hasCompactSupport
        (c1Mollifier j).hasCompactSupport_normed)
      (c1Mollifier j).nonneg_normed (c1Mollifier j).integral_normed _ hV
    intro t ht y hy
    rw [(c1Mollifier j).tsupport_normed_eq] at ht
    have ht' : ‖t‖ ≤ (c1Mollifier (n := n) j).rOut := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using ht
    have hdist : dist y (y + t) = ‖t‖ := by simp [dist_eq_norm]
    exact (dist_triangle y (y + t) c).trans_lt (by
      rw [hdist]
      linarith [Metric.mem_ball.mp hy])
  have hnorm : ∀ x, ‖gradient u x‖ = ‖fderiv ℝ u x‖ := fun x ↦
    (InnerProductSpace.toDual ℝ (Euc n)).symm.norm_map _
  calc
    _ = ∫ x in Metric.closedBall c R, φ x * ‖gradient u x‖ := by
      apply setIntegral_congr_fun measurableSet_closedBall
      intro x hx
      change ‖fderiv ℝ u x‖ = φ x * ‖gradient u x‖
      rw [φ.one_of_mem_closedBall hx, one_mul, hnorm]
    _ ≤ ∫ x, φ x * ‖gradient u x‖ :=
      setIntegral_le_integral ((φ.continuous.mul (gradient_contDiff hu).continuous.norm).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right)
        (ae_of_all _ fun x ↦ mul_nonneg (φ.nonneg (x := x)) (norm_nonneg _))
    _ ≤ _ := hgrad

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack
open RPI.Boundary
open ContinuousLinearMap
open scoped Convolution

theorem c1Mollify_indicator_norm_le_one {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (j : ℕ) (x : Euc n) :
    ‖c1Mollify (E.indicator (fun _ ↦ (1 : ℝ))) j x‖ ≤ 1 := by
  have hh := dist_convolution_le (μ := (volume : Measure (Euc n)))
    (g := E.indicator (fun _ ↦ (1 : ℝ))) (x₀ := x) (z₀ := 0) (by norm_num : (0 : ℝ) ≤ 1)
    (c1Mollifier j).support_normed_eq.subset (c1Mollifier j).nonneg_normed
    (c1Mollifier j).integral_normed (measurable_const.indicator hE).aestronglyMeasurable
    (fun y _ ↦ by by_cases hy : y ∈ E <;> simp [hy])
  simpa only [c1Mollify, dist_zero_right] using hh

theorem raw_ball_poincare {n : ℕ} {E : Set (Euc n)} (hE : MeasurableSet E)
    (c : Euc n) {R : ℝ} (hR : 0 < R)
    (hP : perimeter E (Metric.ball c (4 * R)) ≠ ⊤) :
    volume.real (E ∩ Metric.closedBall c R) *
        volume.real (Eᶜ ∩ Metric.closedBall c R) ≤
      4 * R * volume.real (Metric.closedBall c R) * 2 ^ n *
        (perimeter E (Metric.ball c (4 * R))).toReal := by
  let B := Metric.closedBall c R
  let μ : Measure (Euc n) := volume.restrict B
  have : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ, B] using
      (isCompact_closedBall c R).measure_lt_top (μ := volume)⟩
  let χ : Euc n → ℝ := E.indicator (fun _ ↦ 1)
  let ψ : Euc n → ℝ := Eᶜ.indicator (fun _ ↦ 1)
  let u : ℕ → Euc n → ℝ := c1Mollify χ
  have hχ : LocallyIntegrable χ volume := indicator_one_locallyIntegrable hE
  have hψ : LocallyIntegrable ψ volume := indicator_one_locallyIntegrable hE.compl
  have hχi : Integrable χ μ := hχ.integrableOn_isCompact (isCompact_closedBall c R)
  have hψi : Integrable ψ μ := hψ.integrableOn_isCompact (isCompact_closedBall c R)
  have hu : ∀ j, ContDiff ℝ ∞ (u j) := fun j ↦
    (c1Mollifier j).hasCompactSupport_normed.contDiff_convolution_left _
      (c1Mollifier j).contDiff_normed hχ
  have hub : ∀ j x, ‖u j x‖ ≤ 1 := c1Mollify_indicator_norm_le_one hE
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun j ↦ u j x) atTop (𝓝 (χ x)) := by
    apply Filter.Eventually.filter_mono (ae_mono Measure.restrict_le_self)
    apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      c1Mollifier_radius_tendsto (K := 2) _ hχ
    apply Eventually.of_forall
    intro j
    dsimp [c1Mollifier]
    linarith
  have hlimp : ∀ᵐ p ∂μ.prod μ,
      Tendsto (fun j ↦ ‖u j p.1 - u j p.2‖) atTop (𝓝 ‖χ p.1 - χ p.2‖) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hlim,
      Measure.quasiMeasurePreserving_snd.ae hlim] with p hp hq
    exact (hp.sub hq).norm
  have hDlim : Tendsto (fun j ↦ ∫ p, ‖u j p.1 - u j p.2‖ ∂μ.prod μ) atTop
      (𝓝 (∫ p, ‖χ p.1 - χ p.2‖ ∂μ.prod μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (2 : ℝ))
    · intro j
      exact (((hu j).continuous.comp continuous_fst).sub
        ((hu j).continuous.comp continuous_snd)).norm.aestronglyMeasurable
    · exact integrable_const _
    · intro j
      apply ae_of_all
      intro p
      simp only [norm_norm]
      exact (norm_sub_le _ _).trans (by linarith [hub j p.1, hub j p.2])
    · exact hlimp
  have hD : (∫ p, ‖χ p.1 - χ p.2‖ ∂μ.prod μ) ≤
      4 * R * volume.real B * 2 ^ n * (perimeter E (Metric.ball c (4 * R))).toReal := by
    apply le_of_tendsto hDlim
    have hsmall : ∀ᶠ j in atTop, (c1Mollifier (n := n) j).rOut < R :=
      c1Mollifier_radius_tendsto.eventually (gt_mem_nhds hR)
    filter_upwards [hsmall] with j hj
    have hh := smooth_ball_poincare ((hu j).of_le (by simp)) c hR
    apply hh.trans
    have hgrad := c1Mollify_indicator_local_gradient_le hE c hR hP j hj
    have hconst : 0 ≤ 4 * R * volume.real B * (2 : ℝ) ^ n := by positivity
    calc
      _ = (4 * R * volume.real B * (2 : ℝ) ^ n) *
          ∫ x in B, ‖fderiv ℝ (u j) x‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hgrad hconst
  have hDi : Integrable (fun p : Euc n × Euc n ↦ ‖χ p.1 - χ p.2‖) (μ.prod μ) :=
    ((hχi.comp_fst μ).sub (hχi.comp_snd μ)).norm
  calc
    _ = (∫ x, χ x ∂μ) * ∫ y, ψ y ∂μ := by
      simp only [χ, ψ, μ, integral_indicator hE, integral_indicator hE.compl,
        Measure.restrict_restrict hE, Measure.restrict_restrict hE.compl,
        integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one, B]
    _ = ∫ p, χ p.1 * ψ p.2 ∂μ.prod μ := (integral_prod_mul χ ψ).symm
    _ ≤ ∫ p, ‖χ p.1 - χ p.2‖ ∂μ.prod μ := by
      apply integral_mono (hχi.mul_prod hψi) hDi
      intro p
      by_cases hp : p.1 ∈ E <;> by_cases hq : p.2 ∈ E <;> simp [χ, ψ, hp, hq]
    _ ≤ _ := hD

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem exists_minimizing_perimeter_lower_density (n : ℕ) (hn : 1 < n) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ E : Set (Euc n), IsLocallyPerimeterMinimizing E →
      ∀ c ∈ perimeterSupport E, ∀ r : ℝ, 0 < r →
        ENNReal.ofReal (c₀ * r ^ (n - 1)) ≤ perimeter E (Metric.ball c r) := by
  have hnr : (1 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨ε, hε, hphase⟩ := minimizing_scaled_two_phase_volume_lower
    (Real.HolderConjugate.conjExponent hnr)
  let V := volume.real (Metric.ball (0 : Euc n) 1)
  have hV : 0 < V := by
    change 0 < volume.real (Metric.ball (0 : Euc n) 1)
    rw [measureReal_def, ENNReal.toReal_pos_iff]
    exact ⟨Metric.measure_ball_pos volume _ (by norm_num),
      (measure_mono Metric.ball_subset_closedBall).trans_lt
        (isCompact_closedBall (0 : Euc n) 1).measure_lt_top⟩
  let K : ℝ := 4 * V * 2 ^ n
  have hK : 0 < K := by dsimp [K]; positivity
  let c₀ : ℝ := ε ^ 2 / (K * 4 ^ (n - 1))
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  refine ⟨c₀, hc₀, ?_⟩
  intro E hmin c hc r hr
  let R := r / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have h4R : 4 * R = r := by dsimp [R]; ring
  have hP : perimeter E (Metric.ball c (4 * R)) ≠ ⊤ :=
    (hmin.2.1 c (4 * R) (by positivity)).ne
  have hpoin := raw_ball_poincare hmin.1 c hR hP
  have hvol : volume.real (Metric.closedBall c R) = R ^ n * V := by
    simpa only [Euc, finrank_euclideanSpace, Fintype.card_fin, V] using
      (Measure.addHaar_real_closedBall (volume : Measure (Euc n)) c hR.le)
  rw [hvol] at hpoin
  obtain ⟨hleft, hright⟩ := hphase E hmin c hc R hR
  have hprod : (ε * R ^ n) * (ε * R ^ n) ≤
      volume.real (E ∩ Metric.closedBall c R) *
        volume.real (Eᶜ ∩ Metric.closedBall c R) :=
    mul_le_mul hleft.le hright.le (by positivity) measureReal_nonneg
  have hpow : R ^ n = R ^ (n - 1) * R := by
    rw [← pow_succ]
    congr 1
    omega
  have hsimple : ε ^ 2 * R ^ (n - 1) ≤ K *
      (perimeter E (Metric.ball c (4 * R))).toReal := by
    apply (mul_le_mul_iff_right₀ (show 0 < R ^ n * R by positivity)).mp
    calc
      _ = (ε * R ^ n) * (ε * R ^ n) := by rw [hpow]; ring
      _ ≤ _ := hprod.trans hpoin
      _ = _ := by dsimp [K]; ring
  have hfinal : c₀ * r ^ (n - 1) ≤ (perimeter E (Metric.ball c r)).toReal := by
    apply (mul_le_mul_iff_right₀ hK).mp
    calc
      K * (c₀ * r ^ (n - 1)) = ε ^ 2 * R ^ (n - 1) := by
        rw [← h4R, mul_pow]
        dsimp [c₀]
        field_simp
      _ ≤ _ := by simpa only [h4R] using hsimple
  exact (ENNReal.ofReal_le_ofReal hfinal).trans_eq (ENNReal.ofReal_toReal
    (hmin.2.1 c r hr).ne)

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem exists_minimizing_surfaceMeasure_growth {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E) :
    ∃ A : ℝ, 0 < A ∧ ∀ (c : Euc n) (r : ℝ), 0 < r →
      RPI.Boundary.surfaceMeasure (perimeterSupport E) (Metric.ball c r) ≤
        ENNReal.ofReal (A * r ^ (n - 1)) := by
  obtain ⟨c₀, hc₀, hdensity₀⟩ := exists_minimizing_perimeter_lower_density n hn
  obtain ⟨C, hC, hperim⟩ := exists_locallyMinimizing_perimeter_growth_constant n (by omega)
  have hdensity : ∀ x ∈ perimeterSupport E, ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (c₀ * r ^ (n - 1)) ≤ perimeter E (Metric.ball x r) := by
    intro x hx
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hdensity₀ E hmin x hx r hr
  let K : ℝ≥0∞ := (8 : ℝ≥0∞) ^ (n - 1) * (ENNReal.ofReal c₀)⁻¹ *
    ENNReal.ofReal C * (2 : ℝ≥0∞) ^ (n - 1)
  have hK : K ≠ ⊤ := by
    unfold K
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by finiteness)
        (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hc₀)))
      ENNReal.ofReal_ne_top) (by finiteness)
  have hraw : ∀ (c : Euc n) (r : ℝ), 0 < r →
      Measure.hausdorffMeasure (n - 1 : ℕ) (Metric.ball c r ∩ perimeterSupport E) ≤
        K * ENNReal.ofReal r ^ (n - 1) := by
    intro c r hr
    rw [inter_comm]
    calc
      _ ≤ (8 : ℝ≥0∞) ^ (n - 1) * (ENNReal.ofReal c₀)⁻¹ *
          perimeter E (Metric.ball c (2 * r)) :=
        hausdorffMeasure_le_perimeter_of_lower_density E (perimeterSupport E) hc₀ hdensity c hr
      _ ≤ (8 : ℝ≥0∞) ^ (n - 1) * (ENNReal.ofReal c₀)⁻¹ *
          ENNReal.ofReal (C * (2 * r) ^ (n - 1)) := by
        exact mul_le_mul le_rfl (hperim E hmin c (2 * r) (by positivity)) (by positivity) (by positivity)
      _ = _ := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num only [ENNReal.ofReal_ofNat]
        simp only [K, mul_pow, mul_assoc]
  let a : ℝ≥0∞ := (Measure.addHaarScalarFactor (volume : Measure (Euc (n - 1)))
    (Measure.hausdorffMeasure ((n - 1 : ℕ) : ℝ)) : ℝ≥0∞)
  let A : ℝ := (a * K).toReal + 1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro c r hr
  have haK : a * K ≤ ENNReal.ofReal A := by
    rw [← ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.coe_ne_top hK)]
    exact ENNReal.ofReal_le_ofReal (by dsimp [A]; linarith)
  rw [RPI.Boundary.surfaceMeasure, Measure.restrict_apply measurableSet_ball,
    Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def]
  change a * Measure.hausdorffMeasure (n - 1 : ℕ) (Metric.ball c r ∩ perimeterSupport E) ≤ _
  calc
    _ ≤ a * (K * ENNReal.ofReal r ^ (n - 1)) :=
      mul_le_mul le_rfl (hraw c r hr) (by positivity) (by positivity)
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal r ^ (n - 1) := by
      rw [← mul_assoc]
      exact mul_le_mul haK le_rfl (by positivity) (by positivity)
    _ = _ := by rw [ENNReal.ofReal_mul hA.le, ENNReal.ofReal_pow hr.le]

end RPISingularHarnack

end

end OAI
