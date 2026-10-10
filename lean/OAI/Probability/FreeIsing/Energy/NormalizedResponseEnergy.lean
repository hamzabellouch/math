import OAI.Probability.FreeIsing.Energy.NormalizedResponseLimit

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem367

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem tsum_lintegral_sq_le_liminf_of_ae_tendsto
    {ι : Type*} [Countable ι] (μ : Measure Ω)
    {X : ℕ → ι → Ω → ℝ} {Y : ι → Ω → ℝ}
    (hX : ∀ n i, AEStronglyMeasurable (X n i) μ)
    (hlim : ∀ i, ∀ᵐ ω ∂μ, Tendsto (fun n => X n i ω) atTop (𝓝 (Y i ω))) :
    (∑' i, ∫⁻ ω, ENNReal.ofReal ((Y i ω) ^ 2) ∂μ) ≤
      liminf (fun n => ∑' i, ∫⁻ ω, ENNReal.ofReal ((X n i ω) ^ 2) ∂μ) atTop := by
  have hcoord (i : ι) : (∫⁻ ω, ENNReal.ofReal ((Y i ω) ^ 2) ∂μ) ≤
      liminf (fun n => ∫⁻ ω, ENNReal.ofReal ((X n i ω) ^ 2) ∂μ) atTop := by
    calc
      _ = ∫⁻ ω, liminf (fun n => ENNReal.ofReal ((X n i ω) ^ 2)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim i] with ω hω
        exact (ENNReal.tendsto_ofReal (hω.pow 2)).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le' (fun n => ((hX n i).aemeasurable.pow_const 2).ennreal_ofReal)
  apply (ENNReal.tsum_le_tsum hcoord).trans
  let : MeasurableSpace ι := ⊤
  have hmeas (n : ℕ) : Measurable
      (fun i => ∫⁻ ω, ENNReal.ofReal ((X n i ω) ^ 2) ∂μ) := measurable_of_countable _
  simpa only [lintegral_count] using
    (lintegral_liminf_le (μ := Measure.count) hmeas)

theorem tsum_lintegral_sq_le_of_ae_tendsto
    {ι : Type*} [Countable ι] (μ : Measure Ω)
    {X : ℕ → ι → Ω → ℝ} {Y : ι → Ω → ℝ} {C : ℝ≥0∞}
    (hX : ∀ n i, AEStronglyMeasurable (X n i) μ)
    (hlim : ∀ i, ∀ᵐ ω ∂μ, Tendsto (fun n => X n i ω) atTop (𝓝 (Y i ω)))
    (henergy : ∀ n, (∑' i, ∫⁻ ω, ENNReal.ofReal ((X n i ω) ^ 2) ∂μ) ≤ C) :
    (∑' i, ∫⁻ ω, ENNReal.ofReal ((Y i ω) ^ 2) ∂μ) ≤ C :=
  (tsum_lintegral_sq_le_liminf_of_ae_tendsto μ hX hlim).trans
    (liminf_le_of_frequently_le' (Filter.Frequently.of_forall henergy))

theorem ae_summable_sq_of_tsum_lintegral_sq_ne_top
    {ι : Type*} [Countable ι] (μ : Measure Ω) {Y : ι → Ω → ℝ}
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (henergy : (∑' i, ∫⁻ ω, ENNReal.ofReal ((Y i ω) ^ 2) ∂μ) ≠ ⊤) :
    ∀ᵐ ω ∂μ, Summable (fun i => (Y i ω) ^ 2) := by
  have hfinite : (∫⁻ ω, ∑' i, ENNReal.ofReal ((Y i ω) ^ 2) ∂μ) ≠ ⊤ := by
    rw [lintegral_tsum (fun i => ((hY i).aemeasurable.pow_const 2).ennreal_ofReal)]
    exact henergy
  filter_upwards [ae_lt_top' (AEMeasurable.tsum
    (fun i => ((hY i).aemeasurable.pow_const 2).ennreal_ofReal)) hfinite] with ω hω
  have hs : Summable (fun i => ((Y i ω) ^ 2).toNNReal) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp hω.ne
  have hs' := NNReal.summable_coe.mpr hs
  simpa only [Real.coe_toNNReal', max_eq_left (sq_nonneg _)] using hs'

theorem posteriorResponse_row_energy_le
    {ι : Type*} [Countable ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration ℕ mΩ) (f : Ω → ℝ) (g : ι → Ω → ℝ) {C : ℝ≥0∞}
    (hinterior : ∀ᵐ ω ∂μ, μ[f | ⨆ n, F n] ω ∈ Set.Ioo (-1 : ℝ) 1)
    (henergy : ∀ n, (∑' i, ∫⁻ ω,
      ENNReal.ofReal ((posteriorResponse μ (F n) f (g i) ω) ^ 2) ∂μ) ≤ C) :
    (∑' i, ∫⁻ ω,
      ENNReal.ofReal ((posteriorResponse μ (⨆ n, F n) f (g i) ω) ^ 2) ∂μ) ≤ C := by
  apply tsum_lintegral_sq_le_of_ae_tendsto μ
    (fun n i => ((stronglyMeasurable_posteriorResponse μ (F n) f (g i)).mono
      (F.le n)).aestronglyMeasurable)
    (fun i => tendsto_ae_posteriorResponse μ F f (g i) hinterior) henergy

theorem integrable_tsum_sq_of_tsum_lintegral_sq_ne_top
    {ι : Type*} [Countable ι] (μ : Measure Ω) {Y : ι → Ω → ℝ}
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (henergy : (∑' i, ∫⁻ ω, ENNReal.ofReal ((Y i ω) ^ 2) ∂μ) ≠ ⊤) :
    Integrable (fun ω => ∑' i, (Y i ω) ^ 2) μ := by
  refine ⟨(AEMeasurable.tsum (fun i => (hY i).aemeasurable.pow_const 2)).aestronglyMeasurable, ?_⟩
  have heq : (∫⁻ ω, ‖∑' i, (Y i ω) ^ 2‖ₑ ∂μ) =
      ∑' i, ∫⁻ ω, ENNReal.ofReal ((Y i ω) ^ 2) ∂μ := by
    rw [← lintegral_tsum (fun i => ((hY i).aemeasurable.pow_const 2).ennreal_ofReal)]
    apply lintegral_congr_ae
    filter_upwards [ae_summable_sq_of_tsum_lintegral_sq_ne_top μ hY henergy] with ω hω
    rw [Real.enorm_of_nonneg (tsum_nonneg (fun i => sq_nonneg _))]
    exact ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hω
  change (∫⁻ ω, ‖∑' i, (Y i ω) ^ 2‖ₑ ∂μ) < ⊤
  rw [heq]
  exact henergy.lt_top

theorem integral_tsum_sq_le_of_tsum_lintegral_sq_le
    {ι : Type*} [Countable ι] (μ : Measure Ω) {Y : ι → Ω → ℝ} {C : ℝ}
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ) (hC : 0 ≤ C)
    (henergy : (∑' i, ∫⁻ ω, ENNReal.ofReal ((Y i ω) ^ 2) ∂μ) ≤ ENNReal.ofReal C) :
    Integrable (fun ω => ∑' i, (Y i ω) ^ 2) μ ∧
      (∫ ω, ∑' i, (Y i ω) ^ 2 ∂μ) ≤ C := by
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top henergy
  have hint := integrable_tsum_sq_of_tsum_lintegral_sq_ne_top μ hY hfinite
  refine ⟨hint, ?_⟩
  have heq : ENNReal.ofReal (∫ ω, ∑' i, (Y i ω) ^ 2 ∂μ) =
      ∑' i, ∫⁻ ω, ENNReal.ofReal ((Y i ω) ^ 2) ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun ω => tsum_nonneg (fun i => sq_nonneg _)))]
    rw [← lintegral_tsum (fun i => ((hY i).aemeasurable.pow_const 2).ennreal_ofReal)]
    apply lintegral_congr_ae
    filter_upwards [ae_summable_sq_of_tsum_lintegral_sq_ne_top μ hY hfinite] with ω hω
    exact ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hω
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp (heq.trans_le henergy)

end Problem367

end

end OAI
