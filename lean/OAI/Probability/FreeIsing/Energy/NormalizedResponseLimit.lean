import OAI.Probability.FreeIsing.Conditioning.CovarianceLimit

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def posteriorResponse (μ : Measure Ω) (m : MeasurableSpace Ω)
    (f g : Ω → ℝ) (ω : Ω) : ℝ :=
  posteriorCovariance (mΩ := mΩ) μ m f g ω / (1 - (μ[f | m] ω) ^ 2)

lemma stronglyMeasurable_posteriorResponse (μ : Measure Ω)
    (m : MeasurableSpace Ω) (f g : Ω → ℝ) :
    StronglyMeasurable[m] (posteriorResponse (mΩ := mΩ) μ m f g) :=
  (stronglyMeasurable_posteriorCovariance (mΩ := mΩ) μ m f g).div
    (stronglyMeasurable_const.sub (stronglyMeasurable_condExp.pow 2))

lemma abs_covariance_le_variance_of_binary_moment_bounds
    {a b c : ℝ} (ha : |a| ≤ 1)
    (h₁ : c ≤ 1 + a - b) (h₂ : c ≤ 1 - a + b)
    (h₃ : -1 - a - b ≤ c) (h₄ : -1 + a + b ≤ c) :
    |c - a * b| ≤ 1 - a ^ 2 := by
  have ham : 0 ≤ 1 - a := by linarith only [(abs_le.mp ha).2]
  have hap : 0 ≤ 1 + a := by linarith only [(abs_le.mp ha).1]
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg ham (show 0 ≤ 1 + a + b + c by linarith),
      mul_nonneg hap (show 0 ≤ 1 - a - b + c by linarith)]
  · nlinarith [mul_nonneg ham (show 0 ≤ 1 + a - b - c by linarith),
      mul_nonneg hap (show 0 ≤ 1 - a + b - c by linarith)]

theorem ae_abs_posteriorCovariance_le_binary_variance
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hbinary : ∀ᵐ ω ∂μ, f ω = -1 ∨ f ω = 1)
    (hgb : ∀ᵐ ω ∂μ, |g ω| ≤ 1) :
    ∀ᵐ ω ∂μ, |posteriorCovariance (mΩ := mΩ) μ m f g ω| ≤ 1 - (μ[f | m] ω) ^ 2 := by
  have hfb : ∀ᵐ ω ∂μ, |f ω| ≤ 1 := by
    filter_upwards [hbinary] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  have hfg : Integrable (fun ω => f ω * g ω) μ := by
    apply Integrable.of_bound (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) 1
    filter_upwards [hfb, hgb] with ω hfw hgw
    simpa only [Real.norm_eq_abs, Pi.mul_apply, abs_mul, one_mul] using
      mul_le_mul hfw hgw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h₁ : (fun ω => f ω * g ω) ≤ᵐ[μ] (fun ω => 1 + f ω - g ω) := by
    filter_upwards [hbinary, hgb] with ω hω hgω
    rcases hω with hω | hω <;> rw [hω] <;> nlinarith [(abs_le.mp hgω).1, (abs_le.mp hgω).2]
  have h₂ : (fun ω => f ω * g ω) ≤ᵐ[μ] (fun ω => 1 - f ω + g ω) := by
    filter_upwards [hbinary, hgb] with ω hω hgω
    rcases hω with hω | hω <;> rw [hω] <;> nlinarith [(abs_le.mp hgω).1, (abs_le.mp hgω).2]
  have h₃ : (fun ω => -1 - f ω - g ω) ≤ᵐ[μ] (fun ω => f ω * g ω) := by
    filter_upwards [hbinary, hgb] with ω hω hgω
    rcases hω with hω | hω <;> rw [hω] <;> nlinarith [(abs_le.mp hgω).1, (abs_le.mp hgω).2]
  have h₄ : (fun ω => -1 + f ω + g ω) ≤ᵐ[μ] (fun ω => f ω * g ω) := by
    filter_upwards [hbinary, hgb] with ω hω hgω
    rcases hω with hω | hω <;> rw [hω] <;> nlinarith [(abs_le.mp hgω).1, (abs_le.mp hgω).2]
  have hc₁ := condExp_mono (m := m) hfg (((integrable_const (1 : ℝ)).add hf).sub hg) h₁
  have hc₂ := condExp_mono (m := m) hfg (((integrable_const (1 : ℝ)).sub hf).add hg) h₂
  have hc₃ := condExp_mono (m := m) (((integrable_const (-1 : ℝ)).sub hf).sub hg) hfg h₃
  have hc₄ := condExp_mono (m := m) (((integrable_const (-1 : ℝ)).add hf).add hg) hfg h₄
  filter_upwards [hc₁, hc₂, hc₃, hc₄,
    condExp_sub ((integrable_const (1 : ℝ)).add hf) hg m,
    condExp_add (integrable_const (1 : ℝ)) hf m,
    condExp_add ((integrable_const (1 : ℝ)).sub hf) hg m,
    condExp_sub (integrable_const (1 : ℝ)) hf m,
    condExp_sub ((integrable_const (-1 : ℝ)).sub hf) hg m,
    condExp_sub (integrable_const (-1 : ℝ)) hf m,
    condExp_add ((integrable_const (-1 : ℝ)).add hf) hg m,
    condExp_add (integrable_const (-1 : ℝ)) hf m,
    ae_bdd_abs_condExp_of_ae_bdd_abs (m := m) hfb]
    with ω hc₁ hc₂ hc₃ hc₄ he₁ he₂ he₃ he₄ he₅ he₆ he₇ he₈ hb
  simp only [Pi.add_apply, Pi.sub_apply, condExp_const hm] at *
  exact abs_covariance_le_variance_of_binary_moment_bounds
    (a := μ[f | m] ω) (b := μ[g | m] ω)
    (c := μ[fun x => f x * g x | m] ω) hb
    (by linarith) (by linarith) (by linarith) (by linarith)

theorem ae_abs_posteriorResponse_le_one
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hbinary : ∀ᵐ ω ∂μ, f ω = -1 ∨ f ω = 1)
    (hgb : ∀ᵐ ω ∂μ, |g ω| ≤ 1) :
    ∀ᵐ ω ∂μ, |posteriorResponse (mΩ := mΩ) μ m f g ω| ≤ 1 := by
  filter_upwards [ae_abs_posteriorCovariance_le_binary_variance (mΩ := mΩ) μ m hm hf hg hbinary hgb]
    with ω hω
  have hnonneg : 0 ≤ 1 - (μ[f | m] ω) ^ 2 := (abs_nonneg _).trans hω
  change |posteriorCovariance (mΩ := mΩ) μ m f g ω / (1 - (μ[f | m] ω) ^ 2)| ≤ 1
  by_cases hz : 1 - (μ[f | m] ω) ^ 2 = 0
  · simp [hz]
  · rw [abs_div, abs_of_nonneg hnonneg]
    exact (div_le_one (lt_of_le_of_ne hnonneg (Ne.symm hz))).mpr hω

theorem tendsto_ae_posteriorResponse
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Filtration ℕ mΩ)
    (f g : Ω → ℝ)
    (hinterior : ∀ᵐ ω ∂μ, μ[f | ⨆ n, F n] ω ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => posteriorResponse μ (F n) f g ω) atTop
      (𝓝 (posteriorResponse μ (⨆ n, F n) f g ω)) := by
  filter_upwards [tendsto_ae_posteriorCovariance μ F f g,
    tendsto_ae_condExp (μ := μ) (ℱ := F) f, hinterior] with ω hc hm hi
  have hden : 1 - (μ[f | ⨆ n, F n] ω) ^ 2 ≠ 0 := by
    have hsq : (μ[f | ⨆ n, F n] ω) ^ 2 < 1 := by
      nlinarith [mul_pos (show 0 < 1 - μ[f | ⨆ n, F n] ω by linarith [hi.2])
        (show 0 < 1 + μ[f | ⨆ n, F n] ω by linarith [hi.1])]
    exact ne_of_gt (sub_pos.mpr hsq)
  exact hc.div (tendsto_const_nhds.sub (hm.pow 2)) hden

theorem tendsto_integral_sq_sub_posteriorResponse
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Filtration ℕ mΩ)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hbinary : ∀ᵐ ω ∂μ, f ω = -1 ∨ f ω = 1)
    (hgb : ∀ᵐ ω ∂μ, |g ω| ≤ 1)
    (hinterior : ∀ᵐ ω ∂μ, μ[f | ⨆ n, F n] ω ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto (fun n => ∫ ω,
      (posteriorResponse μ (F n) f g ω -
        posteriorResponse μ (⨆ n, F n) f g ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  apply tendsto_integral_sq_sub_of_bounded_ae μ
    (fun n => ((stronglyMeasurable_posteriorResponse μ (F n) f g).mono
      (F.le n)).aestronglyMeasurable)
    (((stronglyMeasurable_posteriorResponse μ (⨆ n, F n) f g).mono
      (iSup_le fun n => F.le n)).aestronglyMeasurable) (by norm_num : (0 : ℝ) ≤ 1)
  · intro n
    simpa only [Real.norm_eq_abs] using
      ae_abs_posteriorResponse_le_one μ (F n) (F.le n) hf hg hbinary hgb
  · simpa only [Real.norm_eq_abs] using
      ae_abs_posteriorResponse_le_one μ (⨆ n, F n) (iSup_le fun n => F.le n)
        hf hg hbinary hgb
  · exact tendsto_ae_posteriorResponse μ F f g hinterior

end Problem367

end

end OAI
