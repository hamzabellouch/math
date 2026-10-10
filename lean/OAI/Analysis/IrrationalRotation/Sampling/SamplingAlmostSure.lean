import Mathlib

namespace OAI

open Filter MeasureTheory
open scoped ENNReal Topology

namespace Invariant233.ProductSampling

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem ae_summable_of_lintegral_tsum_ne_top {e : ℕ → Ω → ℝ}
    (he : ∀ n ω, 0 ≤ e n ω)
    (hmeas : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal (e n ω)) μ)
    (hsum : (∑' n, ∫⁻ ω, ENNReal.ofReal (e n ω) ∂μ) ≠ ∞) :
    ∀ᵐ ω ∂μ, Summable (fun n => e n ω) := by
  have hfinite : ∀ᵐ ω ∂μ, (∑' n, ENNReal.ofReal (e n ω)) < ∞ := by
    apply ae_lt_top' (AEMeasurable.tsum hmeas)
    rwa [lintegral_tsum hmeas]
  filter_upwards [hfinite] with ω hω
  simpa only [ENNReal.toReal_ofReal (he _ _)] using ENNReal.summable_toReal hω.ne

theorem ae_tendsto_zero_of_lintegral_norm_sq_tsum_ne_top
    {E : Type*} [NormedAddCommGroup E] {F : ℕ → Ω → E}
    (hmeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hsum : (∑' n, ∫⁻ ω, ENNReal.ofReal (‖F n ω‖ ^ 2) ∂μ) ≠ ∞) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 0) := by
  have hs : ∀ᵐ ω ∂μ, Summable (fun n => ‖F n ω‖ ^ 2) :=
    ae_summable_of_lintegral_tsum_ne_top (fun _ _ => sq_nonneg _)
      (fun n => ((hmeas n).norm.aemeasurable.pow_const 2).ennreal_ofReal) hsum
  filter_upwards [hs] with ω hω
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hω.tendsto_atTop_zero
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using hsqrt

theorem ae_tendsto_zero_of_summable_expected_norm_sq_bound
    {E : Type*} [NormedAddCommGroup E] {F : ℕ → Ω → E} {b : ℕ → ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hbound : ∀ n, (∫⁻ ω, ENNReal.ofReal (‖F n ω‖ ^ 2) ∂μ) ≤ ENNReal.ofReal (b n))
    (hb : Summable b) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_lintegral_norm_sq_tsum_ne_top hmeas
  exact ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hbound) hb.tsum_ofReal_ne_top.lt_top)

theorem ae_all_tendsto_zero_of_summable_expected_norm_sq_bound
    {ι E : Type*} [Countable ι] [NormedAddCommGroup E]
    {F : ι → ℕ → Ω → E} {b : ι → ℕ → ℝ}
    (hmeas : ∀ i n, AEStronglyMeasurable (F i n) μ)
    (hbound : ∀ i n,
      (∫⁻ ω, ENNReal.ofReal (‖F i n ω‖ ^ 2) ∂μ) ≤ ENNReal.ofReal (b i n))
    (hb : ∀ i, Summable (b i)) :
    ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun n => F i n ω) atTop (𝓝 0) := by
  exact ae_all_iff.mpr (fun i =>
    ae_tendsto_zero_of_summable_expected_norm_sq_bound (hmeas i) (hbound i) (hb i))

theorem exists_all_tendsto_zero_of_summable_expected_norm_sq_bound
    [IsProbabilityMeasure μ] {ι E : Type*} [Countable ι] [NormedAddCommGroup E]
    {F : ι → ℕ → Ω → E} {b : ι → ℕ → ℝ}
    (hmeas : ∀ i n, AEStronglyMeasurable (F i n) μ)
    (hbound : ∀ i n,
      (∫⁻ ω, ENNReal.ofReal (‖F i n ω‖ ^ 2) ∂μ) ≤ ENNReal.ofReal (b i n))
    (hb : ∀ i, Summable (b i)) :
    ∃ ω, ∀ i, Tendsto (fun n => F i n ω) atTop (𝓝 0) :=
  (ae_all_tendsto_zero_of_summable_expected_norm_sq_bound hmeas hbound hb).exists

end Invariant233.ProductSampling

end OAI
