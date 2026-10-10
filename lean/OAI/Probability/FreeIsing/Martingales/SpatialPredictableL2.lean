import OAI.Probability.FreeIsing.Martingales.PredictableL2Completion

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace Problem367.PredictableL2

theorem memLp_two_mul_of_indep
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hind : IndepFun f g μ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    MemLp (fun ω => f ω * g ω) 2 μ := by
  apply (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable.mul
    hg.aestronglyMeasurable)).2
  have hi := (hind.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integrable_mul
    hf.integrable_sq hg.integrable_sq
  simpa only [Function.comp_def, Pi.mul_def, mul_pow, id_eq] using hi

theorem weighted_array_orthogonal
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {H D : Ω → ι → ℝ} (hind : IndepFun H D μ)
    (hH : ∀ i, MemLp (fun ω => H ω i) 2 μ)
    (hD : ∀ i, MemLp (fun ω => D ω i) 2 μ)
    (horth : Pairwise fun i j => ∫ ω, D ω i * D ω j ∂μ = 0) :
    Pairwise fun i j => ∫ ω, (H ω i * D ω i) * (H ω j * D ω j) ∂μ = 0 := by
  intro i j hij
  have hp := hind.comp ((measurable_pi_apply i).mul (measurable_pi_apply j))
    ((measurable_pi_apply i).mul (measurable_pi_apply j))
  have hi := hp.integral_fun_mul_eq_mul_integral
    ((hH i).aestronglyMeasurable.mul (hH j).aestronglyMeasurable)
    ((hD i).aestronglyMeasurable.mul (hD j).aestronglyMeasurable)
  calc
    _ = ∫ ω, (H ω i * H ω j) * (D ω i * D ω j) ∂μ := by
      congr 1
      funext ω
      ring
    _ = (∫ ω, H ω i * H ω j ∂μ) * ∫ ω, D ω i * D ω j ∂μ := hi
    _ = 0 := by rw [horth hij, mul_zero]

theorem independent_weighted_second_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hind : IndepFun f g μ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ ω, (f ω * g ω) ^ 2 ∂μ) =
      (∫ ω, f ω ^ 2 ∂μ) * ∫ ω, g ω ^ 2 ∂μ := by
  have hi := (hind.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integral_fun_mul_eq_mul_integral hf.integrable_sq.aestronglyMeasurable
      hg.integrable_sq.aestronglyMeasurable
  simpa only [Function.comp_def, mul_pow, id_eq] using hi

theorem exists_independent_weighted_sum
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {H D : Ω → ι → ℝ} (hind : IndepFun H D μ)
    (hH : ∀ i, MemLp (fun ω => H ω i) 2 μ)
    (hD : ∀ i, MemLp (fun ω => D ω i) 2 μ)
    (hcenter : ∀ i, ∫ ω, D ω i ∂μ = 0)
    (horth : Pairwise fun i j => ∫ ω, D ω i * D ω j ∂μ = 0)
    (henergy : Summable fun i =>
      (∫ ω, H ω i ^ 2 ∂μ) * ∫ ω, D ω i ^ 2 ∂μ) :
    ∃ Y : Ω → ℝ, Measurable Y ∧ MemLp Y 2 μ ∧
      (∫ ω, Y ω ∂μ) = 0 ∧
      (∫ ω, Y ω ^ 2 ∂μ) =
        ∑' i, (∫ ω, H ω i ^ 2 ∂μ) * ∫ ω, D ω i ^ 2 ∂μ ∧
      Tendsto (fun s : Finset ι => ∫ ω,
        ((∑ i ∈ s, H ω i * D ω i) - Y ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hc (i : ι) : IndepFun (fun ω => H ω i) (fun ω => D ω i) μ :=
    hind.comp (measurable_pi_apply i) (measurable_pi_apply i)
  have hHD (i : ι) : MemLp (fun ω => H ω i * D ω i) 2 μ :=
    memLp_two_mul_of_indep (hc i) (hH i) (hD i)
  have hsecond (i : ι) : (∫ ω, (H ω i * D ω i) ^ 2 ∂μ) =
      (∫ ω, H ω i ^ 2 ∂μ) * ∫ ω, D ω i ^ 2 ∂μ :=
    independent_weighted_second_moment (hc i) (hH i) (hD i)
  obtain ⟨Y, hY, hmY, hsY, hiY⟩ := exists_orthogonal_sum
    (fun i ω => H ω i * D ω i) hHD (weighted_array_orthogonal hind hH hD horth)
    (by simpa only [hsecond] using henergy)
  refine ⟨Y, hmY, hY, ?_, by simpa only [hsecond] using hiY, ?_⟩
  · apply integral_eq_zero_of_hasSum (fun i ω => H ω i * D ω i) hHD hY hsY
    intro i
    rw [(hc i).integral_fun_mul_eq_mul_integral
      (hH i).aestronglyMeasurable (hD i).aestronglyMeasurable, hcenter i, mul_zero]
  · exact tendsto_integral_sq_error_of_hasSum (fun i ω => H ω i * D ω i) hHD hY hsY

end Problem367.PredictableL2

end

end OAI
