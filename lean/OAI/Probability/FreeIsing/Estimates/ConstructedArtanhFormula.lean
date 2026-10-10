import OAI.Probability.FreeIsing.Estimates.NNRealArtanhFormula
import OAI.Probability.FreeIsing.Martingales.UniformIntegral

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.ConstructedArtanhFormula

open ArtanhMartingaleFormula

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem exists_artanh_decomposition [IsProbabilityMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M A a : ℝ≥0 → Ω → ℝ} (T : ℝ≥0)
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hMm : Measurable (fun p : ℝ≥0 × Ω => M p.1 p.2))
    (hcM : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) (Icc 0 T))
    (hcA : ∀ᵐ ω ∂μ, ContinuousOn (fun t => A t ω) (Icc 0 T))
    (hmonoA : ∀ᵐ ω ∂μ, MonotoneOn (fun t => A t ω) (Icc 0 T))
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hbound : ∀ᵐ ω ∂μ, ∀ t, |M t ω| ≤ r)
    {C : ℝ} (hC : 0 ≤ C) (htotal : ∀ᵐ ω ∂μ, A T ω - A 0 ω ≤ C)
    (ha : Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod μ))
    (hprimitive : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      A t ω = A 0 ω + nnrealTimePrimitive a t ω) :
    ∃ L : Ω → ℝ, StronglyMeasurable L ∧ MemLp L 2 μ ∧
      Tendsto (fun n => ∫ ω,
        (BrownianGrid.uniformSum M (fun t ω => firstWeight (M t ω)) T n ω - L ω) ^ 2 ∂μ)
        atTop (𝓝 0) ∧
      (fun ω => Real.artanh (M T ω) - Real.artanh (M 0 ω)) =ᵐ[μ]
        fun ω => L ω + nnrealTimePrimitive
          (fun t ω => secondWeight (M t ω) * a t ω) T ω := by
  let H : ℝ≥0 → Ω → ℝ := fun t ω => firstWeight (M t ω)
  have hd : 0 < 1 - r ^ 2 := by nlinarith
  have hM2 (t : ℝ≥0) : MemLp (M t) 2 μ := by
    apply MemLp.of_bound ((hM.stronglyMeasurable t).mono (F.le t)).aestronglyMeasurable r
    filter_upwards [hbound] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hH : StronglyAdapted F H := fun t => stronglyMeasurable_firstWeight (hM.stronglyMeasurable t)
  have hHb (t : ℝ≥0) : ∀ᵐ ω ∂μ, |H t ω| ≤ 1 / (1 - r ^ 2) :=
    hbound.mono (fun ω hω => firstWeight_bound hr0 hr (hω t))
  have hHc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => H t ω) (Icc 0 T) := by
    filter_upwards [hcM, hbound] with ω hc hb
    apply continuousOn_const.div (continuousOn_const.sub (hc.pow 2))
    intro t ht
    have hs : M t ω ^ 2 ≤ r ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr0).2 (hb t)
    change 1 - M t ω ^ 2 ≠ 0
    linarith
  obtain ⟨L, hLm, hL2, hlim⟩ := MartingaleUniformIntegral.exists_uniform_integral_on
    hM hQ hM2 hH T hHc (show 0 ≤ 1 / (1 - r ^ 2) by positivity)
    (fun t _ => hHb t) hmonoA htotal
  have hL1 := tendsto_integral_abs_zero_of_sq
    (fun n ω => BrownianGrid.uniformSum M H T n ω - L ω)
    (fun n => (MartingaleUniformIntegral.uniformSum_memLp hM2 hH hHb T n).sub hL2) hlim
  refine ⟨L, hLm, hL2, hlim, ?_⟩
  apply NNRealArtanhFormula.artanh_eq_stochasticLimit_add_primitive T hM hQ hMm
    hcM hcA hmonoA hr0 hr hbound hC htotal ha hprimitive
    (hL2.integrable (by norm_num))
  simpa only [Function.comp_def, H] using hL1.comp (tendsto_add_atTop_nat 1)

end Problem367.ConstructedArtanhFormula

end

end OAI
