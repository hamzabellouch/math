import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem367.NonnegativeSeriesL1

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}

theorem integrable_tsum_of_nonnegative
    {f : ι → Ω → ℝ} (hf : ∀ i, Integrable (f i) μ)
    (hn : ∀ i ω, 0 ≤ f i ω) (hs : Summable (fun i => ∫ ω, f i ω ∂μ)) :
    (∀ᵐ ω ∂μ, Summable (fun i => f i ω)) ∧
      Integrable (fun ω => ∑' i, f i ω) μ ∧
      (∫ ω, ∑' i, f i ω ∂μ) = ∑' i, ∫ ω, f i ω ∂μ := by
  have hm (i : ι) : AEMeasurable (fun ω => ENNReal.ofReal (f i ω)) μ :=
    (hf i).aemeasurable.ennreal_ofReal
  have hfin : (∫⁻ ω, ∑' i, ENNReal.ofReal (f i ω) ∂μ) < ∞ := by
    rw [lintegral_tsum hm]
    calc
      (∑' i, ∫⁻ ω, ENNReal.ofReal (f i ω) ∂μ) =
          ∑' i, ENNReal.ofReal (∫ ω, f i ω ∂μ) := by
        apply tsum_congr
        intro i
        exact (ofReal_integral_eq_lintegral_ofReal (hf i)
          (Eventually.of_forall (hn i))).symm
      _ < ∞ := hs.tsum_ofReal_lt_top
  have hae : ∀ᵐ ω ∂μ, Summable (fun i => f i ω) := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hfin.ne] with ω hω
    simpa only [ENNReal.toReal_ofReal (hn _ _)] using ENNReal.summable_toReal hω.ne
  have hint : Integrable (fun ω => ∑' i, f i ω) μ := by
    have h := integrable_toReal_of_lintegral_ne_top (AEMeasurable.tsum hm) hfin.ne
    simpa only [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_ne_top),
      ENNReal.toReal_ofReal (hn _ _)] using h
  refine ⟨hae, hint, ?_⟩
  exact (integral_tsum_of_summable_integral_norm hf
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _ _)] using hs)).symm

theorem tendsto_finsetSum_L1_of_nonnegative
    {f : ι → Ω → ℝ} (hf : ∀ i, Integrable (f i) μ)
    (hn : ∀ i ω, 0 ≤ f i ω) (hs : Summable (fun i => ∫ ω, f i ω ∂μ)) :
    Tendsto (fun s : Finset ι => eLpNorm
      ((fun ω => ∑ i ∈ s, f i ω) - (fun ω => ∑' i, f i ω)) 1 μ)
      atTop (𝓝 0) := by
  classical
  obtain ⟨hae, hint, htotal⟩ := integrable_tsum_of_nonnegative hf hn hs
  have heq (s : Finset ι) : eLpNorm
      ((fun ω => ∑ i ∈ s, f i ω) - (fun ω => ∑' i, f i ω)) 1 μ =
      ENNReal.ofReal ((∑' i, ∫ ω, f i ω ∂μ) - ∑ i ∈ s, ∫ ω, f i ω ∂μ) := by
    have hi : Integrable (fun ω => ∑ i ∈ s, f i ω) μ :=
      integrable_finsetSum s (fun i _ => hf i)
    have hnonneg : ∀ᵐ ω ∂μ, 0 ≤ (∑' i, f i ω) - ∑ i ∈ s, f i ω := by
      filter_upwards [hae] with ω hω
      exact sub_nonneg.mpr (hω.sum_le_tsum s (fun i _ => hn i ω))
    rw [eLpNorm_one_eq_lintegral_enorm (hi.sub hint).aestronglyMeasurable]
    calc
      (∫⁻ ω, ‖((fun ω => ∑ i ∈ s, f i ω) - (fun ω => ∑' i, f i ω)) ω‖ₑ ∂μ) =
          ∫⁻ ω, ENNReal.ofReal ((∑' i, f i ω) - ∑ i ∈ s, f i ω) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hnonneg] with ω hω
        simp only [Pi.sub_apply, ← ofReal_norm, Real.norm_eq_abs]
        rw [abs_sub_comm, abs_of_nonneg hω]
      _ = ENNReal.ofReal (∫ ω, (∑' i, f i ω) - ∑ i ∈ s, f i ω ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal (hint.sub hi) hnonneg).symm
      _ = _ := by rw [integral_sub hint hi, htotal, integral_finsetSum s (fun i _ => hf i)]
  have hsum : Tendsto (fun s : Finset ι => ∑ i ∈ s, ∫ ω, f i ω ∂μ)
      atTop (𝓝 (∑' i, ∫ ω, f i ω ∂μ)) := hs.hasSum
  have hlim := hsum.const_sub (∑' i, ∫ ω, f i ω ∂μ)
  simp only [sub_self] at hlim
  simpa only [Function.comp_def, ENNReal.ofReal_zero, heq] using
    (ENNReal.continuous_ofReal.tendsto 0).comp hlim

end Problem367.NonnegativeSeriesL1

end

end OAI
