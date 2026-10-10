import OAI.Probability.FreeIsing.Brownian.ArraySimpleIntegral
import OAI.Probability.FreeIsing.Brownian.FiltrationIntegralProperties

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace Problem367.BrownianArrayIntegral
open BrownianGrid BrownianFiltrationGrid

theorem exists_planted_channel_integrals
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ a, IsPreBrownianReal (B a) (μ a))
    (hmB : ∀ a t, Measurable (B a t))
    (H : ι → ℝ≥0 → S × (ι → Ω) → ℝ)
    (hH : ∀ a, StronglyAdapted (signalArrayFiltration B hmB) (H a))
    (hc : ∀ a, ∀ᵐ x ∂ν.prod (Measure.infinitePi μ), Continuous (fun t => H a t x))
    (C : ι → ℝ) (hC : ∀ a, 0 ≤ C a)
    (hb : ∀ a, ∀ᵐ x ∂ν.prod (Measure.infinitePi μ), ∀ t, |H a t x| ≤ C a)
    (T : ℝ≥0) :
    ∃ I : ι → S × (ι → Ω) → ℝ,
      (∀ a, MemLp (I a) 2 (ν.prod (Measure.infinitePi μ))) ∧
      (∀ a, StronglyMeasurable (I a)) ∧
      (∀ a, AEStronglyMeasurable[signalArrayFiltration B hmB T]
        (I a) (ν.prod (Measure.infinitePi μ))) ∧
      (∀ a, (∫ x, I a x ∂ν.prod (Measure.infinitePi μ)) = 0) ∧
      (∀ a, (∫ x, I a x ^ 2 ∂ν.prod (Measure.infinitePi μ)) =
        ∫ t in (0 : ℝ)..(T : ℝ), ∫ x, H a t.toNNReal x ^ 2 ∂ν.prod (Measure.infinitePi μ)) ∧
      (Pairwise fun a b => ∫ x, I a x * I b x ∂ν.prod (Measure.infinitePi μ) = 0) ∧
      (∀ a, Tendsto (fun n => ∫ x,
        (BrownianGrid.uniformSum (fun t x => B a t (x.2 a)) (H a) T n x - I a x) ^ 2
          ∂ν.prod (Measure.infinitePi μ)) atTop (𝓝 0)) := by
  have (a : ι) : IsProbabilityMeasure (μ a) := (hB a).isGaussianProcess.isProbabilityMeasure
  let P := ν.prod (Measure.infinitePi μ)
  let F := signalArrayFiltration (S := S) B hmB
  let W : ι → ℝ≥0 → S × (ι → Ω) → ℝ := fun a t x => B a t (x.2 a)
  have hW (a : ι) : IsPreBrownianReal (W a) P := planted_coordinate_preBrownian ν μ hB a
  have hAd (a : ι) : StronglyAdapted F (W a) :=
    (preBrownian_martingale_signalArrayFiltration ν μ hB hmB a).stronglyAdapted
  have hi (a : ι) (s t : ℝ≥0) (hst : s ≤ t) :
      Indep (MeasurableSpace.comap (fun x => W a t x - W a s x) inferInstance) (F s) P := by
    change Indep _ (signalArrayFiltration B hmB s) P
    rw [signalArrayFiltration_eq_comap]
    exact (planted_array_increments_indep_signal_past ν μ hB hmB hst).comp
      (measurable_pi_apply a) measurable_id
  have hmH (a : ι) (t : ℝ≥0) : AEStronglyMeasurable (H a t) P :=
    ((hH a t).mono (F.le t)).aestronglyMeasurable
  have hH2 (a : ι) (t : ℝ≥0) : MemLp (H a t) 2 P := by
    apply MemLp.of_bound (hmH a t) (C a)
    filter_upwards [hb a] with x hx
    simpa only [Real.norm_eq_abs] using hx t
  have hex (a : ι) := BrownianFiltrationGrid.exists_uniformSumLp_limit
    (hW a) (hAd a) (hi a) (H a) (hH a) (hH2 a) T
    (fun _ hε => MeanSquareContinuity.uniform_integral_sq_sub_le (hmH a) (hc a) (hC a) (hb a) T hε)
  choose I hI using hex
  have hprop (a : ι) := BrownianFiltrationGrid.uniformSumLp_limit_terminal_centered
    (hW a) (hAd a) (hi a) (H a) (hH a) (hH2 a) T (hI a)
  refine ⟨fun a => I a, fun a => Lp.memLp (I a), fun a => Lp.stronglyMeasurable (I a),
    fun a => (hprop a).1, fun a => (hprop a).2, ?_, ?_, ?_⟩
  · intro a
    exact BrownianFiltrationGrid.uniformSumLp_limit_isometry
      (hW a) (hAd a) (hi a) (H a) (hH a) (hH2 a) (hc a) (hC a) (hb a) T (hI a)
  · intro a b hab
    have hlim := (hI a).inner (𝕜 := ℝ) (hI b)
    have hz (n : ℕ) : inner ℝ
        (BrownianFiltrationGrid.uniformSumLp (hW a) (hAd a) (hi a) (H a) (hH a) (hH2 a) T n)
        (BrownianFiltrationGrid.uniformSumLp (hW b) (hAd b) (hi b) (H b) (hH b) (hH2 b) T n) = 0 := by
      rw [BrownianFiltrationGrid.uniformSumLp, BrownianFiltrationGrid.uniformSumLp,
        PredictableL2.inner_toLp]
      exact planted_grid_sums_orthogonal ν μ hB hmB (uniformGrid T n) (uniformGrid_mono T n)
        (fun a k => H a (uniformGrid T n k)) (fun a k => hH a _) (fun a k => hH2 a _)
        hab (Finset.range n) (Finset.range n)
    have heq : inner ℝ (I a) (I b) = 0 :=
      tendsto_nhds_unique hlim (by simpa only [hz] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    rw [L2.inner_def] at heq
    simpa only [Real.inner_apply] using heq
  · intro a
    exact BrownianFiltrationGrid.integral_sq_error_tendsto_of_Lp_tendsto
      (hW a) (hAd a) (hi a) (H a) (hH a) (hH2 a) T (hI a)

theorem exists_planted_infinite_integral
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ a, IsPreBrownianReal (B a) (μ a))
    (hmB : ∀ a t, Measurable (B a t))
    (H : ι → ℝ≥0 → S × (ι → Ω) → ℝ)
    (hH : ∀ a, StronglyAdapted (signalArrayFiltration B hmB) (H a))
    (hc : ∀ a, ∀ᵐ x ∂ν.prod (Measure.infinitePi μ), Continuous (fun t => H a t x))
    (C : ι → ℝ) (hC : ∀ a, 0 ≤ C a)
    (hb : ∀ a, ∀ᵐ x ∂ν.prod (Measure.infinitePi μ), ∀ t, |H a t x| ≤ C a)
    (T : ℝ≥0)
    (henergy : Summable fun a =>
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ x, H a t.toNNReal x ^ 2 ∂ν.prod (Measure.infinitePi μ)) :
    ∃ (I : ι → S × (ι → Ω) → ℝ) (Y : S × (ι → Ω) → ℝ),
      (∀ a, MemLp (I a) 2 (ν.prod (Measure.infinitePi μ))) ∧
      (∀ a, Tendsto (fun n => ∫ x,
        (BrownianGrid.uniformSum (fun t x => B a t (x.2 a)) (H a) T n x - I a x) ^ 2
          ∂ν.prod (Measure.infinitePi μ)) atTop (𝓝 0)) ∧
      Measurable Y ∧ MemLp Y 2 (ν.prod (Measure.infinitePi μ)) ∧
      (∫ x, Y x ∂ν.prod (Measure.infinitePi μ)) = 0 ∧
      (∫ x, Y x ^ 2 ∂ν.prod (Measure.infinitePi μ)) =
        ∑' a, ∫ t in (0 : ℝ)..(T : ℝ), ∫ x, H a t.toNNReal x ^ 2 ∂ν.prod (Measure.infinitePi μ) ∧
      Tendsto (fun s : Finset ι => ∫ x,
        ((∑ a ∈ s, I a x) - Y x) ^ 2 ∂ν.prod (Measure.infinitePi μ)) atTop (𝓝 0) := by
  have (a : ι) : IsProbabilityMeasure (μ a) := (hB a).isGaussianProcess.isProbabilityMeasure
  obtain ⟨I, hI2, _, _, hz, hiso, horth, happrox⟩ :=
    exists_planted_channel_integrals ν μ hB hmB H hH hc C hC hb T
  obtain ⟨Y, hY, hmY, hsY, heY⟩ := PredictableL2.exists_orthogonal_sum I hI2 horth
    (by simpa only [hiso] using henergy)
  refine ⟨I, Y, hI2, happrox, hmY, hY, ?_, ?_, ?_⟩
  · exact PredictableL2.integral_eq_zero_of_hasSum I hI2 hY hsY hz
  · simpa only [hiso] using heY
  · exact PredictableL2.tendsto_integral_sq_error_of_hasSum I hI2 hY hsY

end Problem367.BrownianArrayIntegral

end

end OAI
