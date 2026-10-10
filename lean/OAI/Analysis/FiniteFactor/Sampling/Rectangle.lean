import OAI.Analysis.FiniteFactor.Sampling.SmoothedPair
import OAI.Analysis.FiniteFactor.Sampling.SmoothingLaw

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem integrable_unit_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs,abs_of_nonneg (hbound x).1] using (hbound x).2)

theorem product_difference_unit_bound (a b c d : ℝ)
    (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) :
    |a*b-c*d| ≤ |a-c|+|b-d| := by
  calc
    _ = |(a-c)*b+c*(b-d)| := by congr 1; ring
    _ ≤ |(a-c)*b|+|c*(b-d)| := abs_add_le _ _
    _ = |a-c| *b+c*|b-d| := by rw [abs_mul,abs_mul,abs_of_nonneg hb.1,abs_of_nonneg hc.1]
    _ ≤ |a-c|+|b-d| := by nlinarith [abs_nonneg (a-c),abs_nonneg (b-d)]

/-- Uniform marginal smoothing errors control a product test under a
possibly dependent joint law. -/
theorem integral_product_smoothing_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g a b : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (ha : Measurable a) (hb : Measurable b)
    (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hab : ∀ x, 0 ≤ a x ∧ a x ≤ 1) (hbb : ∀ x, 0 ≤ b x ∧ b x ≤ 1) :
    |(∫ x, f x*g x ∂μ)-(∫ x, a x*b x ∂μ)| ≤
      (∫ x, |f x-a x| ∂μ)+(∫ x, |g x-b x| ∂μ) := by
  have hfg : Integrable (fun x => f x*g x) μ := integrable_unit_bounded μ _ (hf.mul hg)
    (fun x => ⟨mul_nonneg (hfb x).1 (hgb x).1, by nlinarith [(hfb x).1,(hfb x).2,(hgb x).1,(hgb x).2]⟩)
  have habi : Integrable (fun x => a x*b x) μ := integrable_unit_bounded μ _ (ha.mul hb)
    (fun x => ⟨mul_nonneg (hab x).1 (hbb x).1, by nlinarith [(hab x).1,(hab x).2,(hbb x).1,(hbb x).2]⟩)
  have hfa := (integrable_unit_bounded μ f hf hfb).sub (integrable_unit_bounded μ a ha hab)
  have hgb' := (integrable_unit_bounded μ g hg hgb).sub (integrable_unit_bounded μ b hb hbb)
  have hfa' : Integrable (fun x => |f x-a x|) μ := by simpa [Real.norm_eq_abs] using hfa.norm
  have hgb'' : Integrable (fun x => |g x-b x|) μ := by simpa [Real.norm_eq_abs] using hgb'.norm
  rw [← integral_sub hfg habi]
  calc
    _ ≤ ∫ x, |f x*g x-a x*b x| ∂μ := by simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x*g x-a x*b x)
    _ ≤ ∫ x, |f x-a x|+|g x-b x| ∂μ := by
      apply integral_mono_ae
      · simpa [Real.norm_eq_abs] using (hfg.sub habi).norm
      · exact hfa'.add hgb''
      · exact Filter.Eventually.of_forall (fun x => product_difference_unit_bound _ _ _ _ (hgb x) (hab x))
    _ = _ := integral_add hfa' hgb''

/-- Explicit rectangle discrepancy derived from actual marginal domination
and joint Fourier estimates. No two-dimensional density is required. -/
theorem sampling_rectangle_discrepancy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hdomX : μ.map X ≤ (2 : ℝ≥0∞) • unitIntervalMeasure)
    (hdomY : μ.map Y ≤ (2 : ℝ≥0∞) • unitIntervalMeasure)
    (H : ℕ) (hH : 0 < H) (a b a' b' δ ε : ℝ) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hFourier : ∀ v w : ℤ, |v| < (H : ℤ) → |w| < (H : ℤ) → (v ≠ 0 ∨ w ≠ 0) →
      ‖∫ θ, samplingCharacter v (X θ)*samplingCharacter w (Y θ) ∂μ‖ ≤ ε) :
    |(μ {θ | X θ ∈ Set.Icc a b ∧ Y θ ∈ Set.Icc a' b'}).toReal -
      (unitIntervalMeasure (Set.Icc a b)).toReal*(unitIntervalMeasure (Set.Icc a' b')).toReal| ≤
      24*δ+1/(2*(H : ℝ)*δ^2)+(H : ℝ)^2*ε := by
  let E := Set.Icc a b
  let E' := Set.Icc a' b'
  let f := fun θ => E.indicator (fun _ => (1 : ℝ)) (X θ)
  let g := fun θ => E'.indicator (fun _ => (1 : ℝ)) (Y θ)
  let A := fun θ => samplingSmooth H E (X θ)
  let B := fun θ => samplingSmooth H E' (Y θ)
  have hf : Measurable f := (measurable_const.indicator measurableSet_Icc).comp hX
  have hg : Measurable g := (measurable_const.indicator measurableSet_Icc).comp hY
  have hA : Measurable A := (samplingSmooth_continuous H E).measurable.comp hX
  have hB : Measurable B := (samplingSmooth_continuous H E').measurable.comp hY
  have hfb (θ) : 0 ≤ f θ ∧ f θ ≤ 1 := by
    dsimp [f]; by_cases he : X θ ∈ E <;> simp [he]
  have hgb (θ) : 0 ≤ g θ ∧ g θ ≤ 1 := by
    dsimp [g]; by_cases he : Y θ ∈ E' <;> simp [he]
  have hprod := integral_product_smoothing_error μ f g A B hf hg hA hB hfb hgb
    (fun θ => samplingSmooth_bounds H hH E (X θ)) (fun θ => samplingSmooth_bounds H hH E' (Y θ))
  have : IsProbabilityMeasure (μ.map X) := ⟨by rw [Measure.map_apply hX MeasurableSet.univ]; simp⟩
  have : IsProbabilityMeasure (μ.map Y) := ⟨by rw [Measure.map_apply hY MeasurableSet.univ]; simp⟩
  have hex := samplingSmooth_expected_error (μ.map X) hdomX H hH a b δ hδ
  have hey := samplingSmooth_expected_error (μ.map Y) hdomY H hH a' b' δ hδ
  have hem (a b : ℝ) : Measurable (fun t => |samplingSmooth H (Set.Icc a b) t-
      (Set.Icc a b).indicator (fun _ => (1 : ℝ)) t|) := by
    have hi : Measurable ((Set.Icc a b).indicator (fun _ => (1 : ℝ))) := measurable_const.indicator measurableSet_Icc
    simpa [Real.norm_eq_abs] using ((samplingSmooth_continuous H (Set.Icc a b)).measurable.sub hi).norm
  rw [integral_map hX.aemeasurable (hem a b).aestronglyMeasurable] at hex
  rw [integral_map hY.aemeasurable (hem a' b').aestronglyMeasurable] at hey
  have hfint : (∫ θ, f θ*g θ ∂μ) = (μ {θ | X θ ∈ E ∧ Y θ ∈ E'}).toReal := by
    have he : (fun θ => f θ*g θ) = {θ | X θ ∈ E ∧ Y θ ∈ E'}.indicator (fun _ => (1 : ℝ)) := by
      funext θ
      dsimp [f,g]
      by_cases hx : X θ ∈ E <;> by_cases hy : Y θ ∈ E' <;> simp [hx,hy]
    rw [he,integral_indicator (by exact (hX measurableSet_Icc).inter (hY measurableSet_Icc))]
    simp [measureReal_def]
  have hsm := samplingSmooth_pair_error μ X Y hX hY H hH E E' ε hε hFourier
  simp_rw [← Complex.ofReal_mul] at hsm
  rw [integral_complex_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hsm
  change |(∫ θ, A θ*B θ ∂μ)-(unitIntervalMeasure E).toReal*(unitIntervalMeasure E').toReal| ≤ _ at hsm
  have hex' : (∫ θ, |f θ-A θ| ∂μ) ≤ 12*δ+1/(4*(H : ℝ)*δ^2) := by
    simpa only [f,A,abs_sub_comm] using hex
  have hey' : (∫ θ, |g θ-B θ| ∂μ) ≤ 12*δ+1/(4*(H : ℝ)*δ^2) := by
    simpa only [g,B,abs_sub_comm] using hey
  rw [← hfint]
  have htri := abs_sub_le (∫ θ, f θ*g θ ∂μ) (∫ θ, A θ*B θ ∂μ)
    ((unitIntervalMeasure E).toReal*(unitIntervalMeasure E').toReal)
  have hc : 2*(1/(4*(H : ℝ)*δ^2)) = 1/(2*(H : ℝ)*δ^2) := by ring
  nlinarith

end
end FiniteFactor

end OAI
