import OAI.Probability.FreeIsing.Brownian.ArrayMoments
import OAI.Probability.FreeIsing.Martingales.SpatialPredictableL2

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace Problem367.PredictableL2

theorem planted_coefficients_indep_increments
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t)) {s t : ℝ≥0} (hst : s ≤ t)
    {H : ι → S × (ι → Ω) → ℝ}
    (hH : ∀ i, StronglyMeasurable[signalArrayFiltration B hmB s] (H i)) :
    IndepFun (fun q i => H i q)
      (fun q : S × (ι → Ω) => fun i => B i t (q.2 i) - B i s (q.2 i))
      (ν.prod (Measure.infinitePi μ)) := by
  have hi := (planted_array_increments_indep_signal_past ν μ hB hmB hst).symm
  have hmH : Measurable[signalArrayFiltration B hmB s] (fun q i => H i q) := by
    let : MeasurableSpace (S × (ι → Ω)) := signalArrayFiltration B hmB s
    exact Measurable.of_eval fun i => (hH i).measurable
  apply indep_of_indep_of_le_left hi
  rw [← signalArrayFiltration_eq_comap B hmB s]
  exact hmH.comap_le

theorem exists_planted_spatial_integral
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t)) {s t : ℝ≥0} (hst : s ≤ t)
    (H : ι → S × (ι → Ω) → ℝ)
    (hH : ∀ i, StronglyMeasurable[signalArrayFiltration B hmB s] (H i))
    (hH2 : ∀ i, MemLp (H i) 2 (ν.prod (Measure.infinitePi μ)))
    (henergy : Summable fun i => ∫ q, H i q ^ 2 ∂ν.prod (Measure.infinitePi μ)) :
    ∃ Y : S × (ι → Ω) → ℝ,
      Measurable Y ∧ MemLp Y 2 (ν.prod (Measure.infinitePi μ)) ∧
      (∫ q, Y q ∂ν.prod (Measure.infinitePi μ)) = 0 ∧
      (∫ q, Y q ^ 2 ∂ν.prod (Measure.infinitePi μ)) =
        ((t : ℝ) - (s : ℝ)) *
          ∑' i, ∫ q, H i q ^ 2 ∂ν.prod (Measure.infinitePi μ) ∧
      Tendsto (fun I : Finset ι => ∫ q : S × (ι → Ω),
        ((∑ i ∈ I, H i q * (B i t (q.2 i) - B i s (q.2 i))) - Y q) ^ 2
          ∂ν.prod (Measure.infinitePi μ)) atTop (𝓝 0) := by
  have (i : ι) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := ν.prod (Measure.infinitePi μ)
  let D : S × (ι → Ω) → ι → ℝ := fun q i => B i t (q.2 i) - B i s (q.2 i)
  have hC (i : ι) := planted_coordinate_preBrownian ν μ hB i
  have hD2 (i : ι) : MemLp (fun q => D q i) 2 P :=
    ((hC i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two.sub
      ((hC i).isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hzero (i : ι) : (∫ q, D q i ∂P) = 0 := by
    change (∫ q : S × (ι → Ω), B i t (q.2 i) - B i s (q.2 i) ∂P) = 0
    rw [integral_sub ((hC i).integrable_eval t) ((hC i).integrable_eval s),
      (hC i).integral_eval, (hC i).integral_eval, sub_self]
  have hsq (i : ι) : (∫ q : S × (ι → Ω),
      (B i t (q.2 i) - B i s (q.2 i)) ^ 2 ∂ν.prod (Measure.infinitePi μ)) =
      (t : ℝ) - (s : ℝ) := by
    have hi := preBrownian_integral_sq ((hC i).shift s) (t - s)
    simpa only [add_tsub_cancel_of_le hst, NNReal.coe_sub hst] using hi
  have horth : Pairwise fun i j => ∫ q, D q i * D q j ∂P = 0 := by
    intro i j hij
    have hi := (planted_coordinate_increments_indep ν μ hB hmB s t hij).integral_fun_mul_eq_mul_integral (hD2 i).aestronglyMeasurable (hD2 j).aestronglyMeasurable
    change (∫ q, D q i * D q j ∂P) = (∫ q, D q i ∂P) * ∫ q, D q j ∂P at hi
    simpa only [hzero, zero_mul] using hi
  obtain ⟨Y, hmY, hY, hzY, hiY, htY⟩ := exists_independent_weighted_sum
    (planted_coefficients_indep_increments ν μ hB hmB hst hH) hH2 hD2 hzero horth
    (by simpa only [hsq] using henergy.mul_right ((t : ℝ) - (s : ℝ)))
  refine ⟨Y, hmY, hY, hzY, ?_, htY⟩
  calc
    _ = ∑' i, (∫ q, H i q ^ 2 ∂ν.prod (Measure.infinitePi μ)) *
        ((t : ℝ) - (s : ℝ)) := by simpa only [hsq] using hiY
    _ = (∑' i, ∫ q, H i q ^ 2 ∂ν.prod (Measure.infinitePi μ)) *
        ((t : ℝ) - (s : ℝ)) := tsum_mul_right
    _ = _ := mul_comm _ _

end Problem367.PredictableL2

end

end OAI
