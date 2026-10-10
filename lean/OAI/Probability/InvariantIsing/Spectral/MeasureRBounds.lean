import OAI.Probability.InvariantIsing.Spectral.MeasureInverseContinuity

namespace OAI

/-! Compact-support estimates for the general spectral transform. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical

namespace InvariantIsing

lemma integrable_spectralCoordinate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {l e : ℝ} (hμ : ∀ᵐ y ∂μ, y ∈ Icc l e) : Integrable (fun y => y) μ := by
  apply (integrable_const (|l| + |e|)).mono' measurable_id.aestronglyMeasurable
  filter_upwards [hμ] with y hy
  rw [Real.norm_eq_abs, abs_le]
  simp only [id_eq]
  constructor
  · linarith [neg_abs_le l, abs_nonneg e, hy.1]
  · linarith [le_abs_self e, abs_nonneg l, hy.2]

theorem measureR_bounds_all (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {l e : ℝ} (hμ : ∀ᵐ y ∂μ, y ∈ Icc l e) (x : ℝ) :
    l ≤ measureR μ e x ∧ measureR μ e x ≤ e := by
  by_cases hx : 0 < x
  · exact measureR_bounds μ hμ hx
  · rw [measureR, ite_eq_right hx]
    constructor
    · simpa only [integral_const, probReal_univ, one_smul] using
        integral_mono_ae (integrable_const l) (integrable_spectralCoordinate μ hμ)
          (hμ.mono fun _ h => h.1)
    · simpa only [integral_const, probReal_univ, one_smul] using
        integral_mono_ae (integrable_spectralCoordinate μ hμ) (integrable_const e)
          (hμ.mono fun _ h => h.2)

theorem measureInverse_uncapped_small (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {K e x : ℝ} (hK : 0 < K) (he : e ≤ K)
    (hμ : ∀ᵐ y ∂μ, y ∈ Icc (-K) e) (hx : 0 < x) (hsmall : 4 * K * x ≤ 1) :
    e < measureInverse μ e x ∧ measureResolvent μ (measureInverse μ e x) = x := by
  have htest : e < 1 / x - K := by
    have h := (le_div_iff₀ hx).mpr hsmall
    nlinarith
  have hl := le_measureResolvent μ hμ htest
  have hvalue : x ≤ measureResolvent μ (1 / x - K) := by
    simpa only [sub_neg_eq_add, sub_add_cancel, one_div_one_div] using hl
  have hex := exists_measureResolvent_solution μ (hμ.mono fun _ h => h.2) htest hx hvalue
  obtain ⟨b, hb, hsol⟩ := hex
  rw [measureInverse_eq_of_solution μ (hμ.mono fun _ h => h.2) hb hsol]
  exact ⟨hb, hsol⟩

theorem measureR_sub_mean_identity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {l e x : ℝ} (hμ : ∀ᵐ y ∂μ, y ∈ Icc l e) (hx : 0 < x)
    (hs : e < measureInverse μ e x ∧ measureResolvent μ (measureInverse μ e x) = x) :
    measureR μ e x - ∫ y, y ∂μ =
      ∫ y, (measureR μ e x - y) ^ 2 / (measureInverse μ e x - y) ∂μ := by
  let b := measureInverse μ e x
  have hi := integrable_spectralCoordinate μ hμ
  have hk : Integrable (fun y => 1 / (b - y)) μ :=
    integrable_resolventKernel μ (hμ.mono fun _ h => h.2) hs.1
  have ha : ∀ᵐ y ∂μ, (measureR μ e x - y) ^ 2 / (b - y) =
      (b - y) - 2 / x + (1 / x ^ 2) * (1 / (b - y)) := by
    filter_upwards [hμ] with y hy
    have hby : b - y ≠ 0 := by dsimp only [b]; linarith [hs.1, hy.2]
    simp only [measureR, ite_eq_left hx]
    change (b - 1 / x - y) ^ 2 / (b - y) = _
    field_simp [hx.ne', hby]
    ring
  have hibase : Integrable (fun y => b - y) μ := (integrable_const b).sub hi
  have hib : Integrable (fun y => b - y - 2 / x) μ :=
    hibase.sub (integrable_const (2 / x))
  have hir : Integrable (fun y => (1 / x ^ 2) * (1 / (b - y))) μ := hk.const_mul _
  have hsplit : (∫ y, b - y - 2 / x ∂μ) = b - (∫ y, y ∂μ) - 2 / x := by
    calc
      _ = (∫ y, b - y ∂μ) - (∫ _, 2 / x ∂μ) :=
        integral_sub hibase (integrable_const (2 / x))
      _ = _ := by
        rw [show (∫ y, b - y ∂μ) = (∫ _, b ∂μ) - (∫ y, y ∂μ) from
          integral_sub (integrable_const b) hi]
        simp
  rw [integral_congr_ae ha, integral_add hib hir, hsplit, integral_const_mul]
  change measureR μ e x - (∫ y, y ∂μ) =
    b - (∫ y, y ∂μ) - 2 / x + (1 / x ^ 2) * measureResolvent μ b
  rw [hs.2]
  simp only [measureR, ite_eq_left hx]
  change b - 1 / x - (∫ y, y ∂μ) = _
  field_simp
  ring

theorem measureR_sub_mean_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {K e x : ℝ} (hK : 0 < K) (he : e ≤ K)
    (hμ : ∀ᵐ y ∂μ, y ∈ Icc (-K) e) (hx : 0 < x) (hsmall : 4 * K * x ≤ 1) :
    0 ≤ measureR μ e x - ∫ y, y ∂μ ∧
      measureR μ e x - ∫ y, y ∂μ ≤ 8 * K ^ 2 * x := by
  let b := measureInverse μ e x
  let r := measureR μ e x
  have hs := measureInverse_uncapped_small μ hK he hμ hx hsmall
  have hr := measureR_bounds μ hμ hx
  have hbr : x * b = x * r + 1 := by
    dsimp only [b, r]
    simp only [measureR, ite_eq_left hx]
    field_simp
    ring
  have hb : ∀ᵐ y ∂μ, 0 ≤ (r - y) ^ 2 / (b - y) ∧
      (r - y) ^ 2 / (b - y) ≤ 8 * K ^ 2 * x := by
    filter_upwards [hμ] with y hy
    have hden : 0 < b - y := by dsimp only [b]; linarith [hs.1, hy.2]
    have hlo : -2 * K ≤ r - y := by dsimp only [r]; linarith [hr.1, hy.2]
    have hhi : r - y ≤ 2 * K := by dsimp only [r]; linarith [hr.2, hy.1]
    have hsq : (r - y) ^ 2 ≤ 4 * K ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]
    have hinv : 1 / (b - y) ≤ 2 * x := by
      apply (div_le_iff₀ hden).mpr
      have := mul_le_mul_of_nonneg_left hlo hx.le
      nlinarith
    refine ⟨div_nonneg (sq_nonneg _) hden.le, ?_⟩
    calc
      (r - y) ^ 2 / (b - y) = (r - y) ^ 2 * (1 / (b - y)) := by ring
      _ ≤ (4 * K ^ 2) * (2 * x) := mul_le_mul hsq hinv (one_div_pos.mpr hden).le (by positivity)
      _ = 8 * K ^ 2 * x := by ring
  have hm : Measurable (fun y : ℝ => (r - y) ^ 2 / (b - y)) :=
    ((measurable_const.sub measurable_id).pow_const 2).div (measurable_const.sub measurable_id)
  have hi : Integrable (fun y => (r - y) ^ 2 / (b - y)) μ := by
    apply (integrable_const (8 * K ^ 2 * x)).mono' hm.aestronglyMeasurable
    filter_upwards [hb] with y hy
    simpa only [Real.norm_eq_abs, abs_of_nonneg hy.1] using hy.2
  rw [measureR_sub_mean_identity μ hμ hx hs]
  constructor
  · exact integral_nonneg_of_ae (hb.mono fun _ h => h.1)
  · have hu := integral_mono_ae hi (integrable_const (8 * K ^ 2 * x)) (hb.mono fun _ h => h.2)
    simpa only [integral_const, probReal_univ, one_smul] using hu

theorem continuousAt_measureR_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {K e : ℝ} (hK : 0 < K) (he : e ≤ K) (hμ : ∀ᵐ y ∂μ, y ∈ Icc (-K) e) :
    ContinuousAt (measureR μ e) 0 := by
  have herr : ∀ᶠ x : ℝ in 𝓝 0,
      ‖measureR μ e x - ∫ y, y ∂μ‖ ≤ 8 * K ^ 2 * |x| := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / (4 * K) by positivity)] with x hxsmall
    by_cases hx : 0 < x
    · have hsmall : 4 * K * x ≤ 1 := by
        have := (lt_div_iff₀ (show (0 : ℝ) < 4 * K by positivity)).mp hxsmall
        nlinarith
      have hb := measureR_sub_mean_bound μ hK he hμ hx hsmall
      simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1, abs_of_pos hx] using hb.2
    · simp only [measureR, ite_eq_right hx, sub_self, norm_zero]
      positivity
  have ht : Tendsto (fun x : ℝ => 8 * K ^ 2 * |x|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).const_mul (8 * K ^ 2)
  have hl := (tendsto_sub_nhds_zero_iff).mp (squeeze_zero_norm' herr ht)
  simpa only [ContinuousAt, measureR, lt_self_iff_false, ite_false] using hl

theorem continuous_measureR (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {K e : ℝ} (hK : 0 < K) (he : e ≤ K) (hμ : ∀ᵐ y ∂μ, y ∈ Icc (-K) e) :
    Continuous (measureR μ e) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hc : ContinuousAt (fun _ : ℝ => ∫ y, y ∂μ) x := continuousAt_const
    apply hc.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp only [measureR, ite_eq_right (not_lt.mpr (show y < 0 from hy).le)]
  · subst x
    exact continuousAt_measureR_zero μ hK he hμ
  · exact continuousAt_measureR_pos μ (hμ.mono fun _ h => h.2) hx

end InvariantIsing

end

end OAI
