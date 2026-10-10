import OAI.Analysis.KadisonKastler.RegularLocalizationAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # Compact interval cutoffs for regular vectors

These are elementary support and approximation facts for the actual
indicator projections. They do not require a commutant theorem.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
theorem regularIndicator_translate_eq_of_support
    (s q : Set ℝ) (hs : MeasurableSet s) (hq : MeasurableSet q)
    (f : RegularCoreHilbert H) (hf : regularIndicatorProjection s hs f = f)
    (r : ℝ) (hsub : ∀ t, t + r ∈ s → t ∈ q) :
    regularIndicatorProjection q hq (regularTranslateApply r f) = regularTranslateApply r f := by
  have hsupport : ∀ᵐ t : ℝ, t ∉ s → f t = 0 := by
    filter_upwards [regularIndicatorProjection_apply_ae s hs f] with t ht hts
    rw [hf, Set.indicator_of_notMem hts] at ht
    exact ht
  have htranslated := (measurePreserving_add_right volume r).quasiMeasurePreserving.ae
    hsupport
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae q hq (regularTranslateApply r f),
    regularTranslateApply_ae r f, htranslated] with t hcut htrans hzero
  rw [hcut]
  by_cases ht : t ∈ q
  · rw [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht, htrans]
    exact (hzero (fun h => ht (hsub t h))).symm

omit [CompleteSpace H] in
theorem regularIndicator_translate_zero_of_support
    (s q : Set ℝ) (hs : MeasurableSet s) (hq : MeasurableSet q)
    (f : RegularCoreHilbert H) (hf : regularIndicatorProjection s hs f = f)
    (r : ℝ) (hdis : ∀ t, t ∈ q → t + r ∉ s) :
    regularIndicatorProjection q hq (regularTranslateApply r f) = 0 := by
  have hsupport : ∀ᵐ t : ℝ, t ∉ s → f t = 0 := by
    filter_upwards [regularIndicatorProjection_apply_ae s hs f] with t ht hts
    rw [hf, Set.indicator_of_notMem hts] at ht
    exact ht
  have htranslated := (measurePreserving_add_right volume r).quasiMeasurePreserving.ae
    hsupport
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae q hq (regularTranslateApply r f),
    regularTranslateApply_ae r f, htranslated, Lp.coeFn_zero H 2 (volume : Measure ℝ)]
    with t hcut htrans hzero hz
  rw [hcut, hz]
  by_cases ht : t ∈ q
  · rw [Set.indicator_of_mem ht, htrans]
    exact hzero (hdis t ht)
  · rw [Set.indicator_of_notMem ht]
    rfl

omit [CompleteSpace H] in
theorem regularInterval_translate_eq
    {A R r : ℝ} (h : |r| + A ≤ R)
    (f : RegularCoreHilbert H)
    (hf : regularIndicatorProjection (Set.Icc (-A) A) measurableSet_Icc f = f) :
    regularIndicatorProjection (Set.Icc (-R) R) measurableSet_Icc
      (regularTranslateApply r f) = regularTranslateApply r f := by
  apply regularIndicator_translate_eq_of_support _ _ measurableSet_Icc measurableSet_Icc f hf
  intro t ht
  have hr₁ := neg_abs_le r
  have hr₂ := le_abs_self r
  constructor <;> linarith [ht.1, ht.2]

omit [CompleteSpace H] in
theorem regularInterval_translate_zero
    {A R r : ℝ} (h : R + A < |r|)
    (f : RegularCoreHilbert H)
    (hf : regularIndicatorProjection (Set.Icc (-A) A) measurableSet_Icc f = f) :
    regularIndicatorProjection (Set.Icc (-R) R) measurableSet_Icc
      (regularTranslateApply r f) = 0 := by
  apply regularIndicator_translate_zero_of_support _ _ measurableSet_Icc measurableSet_Icc f hf
  intro t ht hs
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr] at h
    linarith [ht.1, hs.2]
  · rw [abs_of_nonpos hr] at h
    linarith [ht.2, hs.1]

omit [CompleteSpace H] in
/-- Symmetric interval projections converge strongly to the identity. -/
theorem regularIntervalProjection_tendsto (f : RegularCoreHilbert H) :
    Tendsto (fun n : ℕ => regularIndicatorProjection
      (Set.Icc (-(n : ℝ)) (n : ℝ)) measurableSet_Icc f) atTop (𝓝 f) := by
  let F (n : ℕ) (t : ℝ) : ℝ :=
    if t ∈ Set.Icc (-(n : ℝ)) (n : ℝ) then 0 else ‖f t‖ ^ 2
  have hi := (Lp.memLp f).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hm (n : ℕ) : AEStronglyMeasurable (F n) volume := by
    exact aestronglyMeasurable_const.piecewise measurableSet_Icc
      (((Lp.aestronglyMeasurable f).norm.pow 2).restrict)
  have hb (n : ℕ) : ∀ᵐ t : ℝ, ‖F n t‖ ≤ ‖f t‖ ^ 2 := by
    apply Eventually.of_forall
    intro t
    dsimp only [F]
    split_ifs <;> simp
  have ht : ∀ᵐ t : ℝ, Tendsto (fun n : ℕ => F n t) atTop (𝓝 0) := by
    apply Eventually.of_forall
    intro t
    apply tendsto_const_nhds.congr'
    have he : ∀ᶠ n : ℕ in atTop, |t| ≤ (n : ℝ) :=
      (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |t|))
    filter_upwards [he] with n hn
    simp only [F]
    have hn' : t ∈ Set.Icc (-(n : ℝ)) (n : ℝ) :=
      ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    simp only [hn', ite_true]
  have hint := tendsto_integral_of_dominated_convergence (fun t : ℝ => ‖f t‖ ^ 2)
    hm hi hb ht
  simp only [integral_zero] at hint
  have he (n : ℕ) : ‖regularIndicatorProjection
      (Set.Icc (-(n : ℝ)) (n : ℝ)) measurableSet_Icc f - f‖ ^ 2 = ∫ t : ℝ, F n t := by
    rw [← regular_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [regularIndicatorProjection_apply_ae
      (Set.Icc (-(n : ℝ)) (n : ℝ)) measurableSet_Icc f,
      Lp.coeFn_sub (regularIndicatorProjection
        (Set.Icc (-(n : ℝ)) (n : ℝ)) measurableSet_Icc f) f] with t hcut hsub
    rw [hsub]
    simp only [Pi.sub_apply, hcut]
    dsimp only [F]
    split_ifs with ht
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq : Tendsto (fun n : ℕ => ‖regularIndicatorProjection
      (Set.Icc (-(n : ℝ)) (n : ℝ)) measurableSet_Icc f - f‖ ^ 2) atTop (𝓝 0) :=
    hint.congr (fun n => (he n).symm)
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using hsqrt

end

end KadisonKastler

end OAI
