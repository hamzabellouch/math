import OAI.Probability.FreeIsing.Brownian.ContinuousIntegral
import OAI.Probability.FreeIsing.Martingales.RandomEvaluation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem stopped_uniform_limit_random_evaluation
    {B H : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hBc : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
    (hH : StronglyAdapted F H)
    {C : ℝ} (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    {T : ℝ≥0} {I : ℝ≥0 → Ω → ℝ}
    (hI : Martingale I F P) (hI2 : ∀ t, MemLp (I t) 2 P)
    (hIc : ∀ᵐ ω ∂P, Continuous (fun t => I t ω))
    (hlim : Tendsto (fun n => ∫ ω,
      (stoppedUniformSum B H T n T ω - I T ω) ^ 2 ∂P) atTop (𝓝 0))
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) (hτT : ∀ ω, τ ω ≤ T) :
    Tendsto (fun n => ∫ ω,
      (stoppedUniformSum B H T n (τ ω) ω - I (τ ω) ω) ^ 2 ∂P) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P := by
    apply MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hS2 (n : ℕ) (t : ℝ≥0) : MemLp (stoppedUniformSum B H T n t) 2 P :=
    BrownianFiltration.stopped_predictable_sum_memLp_two hB hind
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun i => H (BrownianGrid.uniformGrid T n i)) (fun i => hH _) (fun i => hH2 _)
      (Finset.range n) t
  have hSM (n : ℕ) : Martingale (stoppedUniformSum B H T n) F P := by
    apply BrownianFiltration.stopped_predictable_sum_martingale hB hAd hind
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun i => H (BrownianGrid.uniformGrid T n i)) (fun i => hH _) (fun _ => C)
      (fun i => ?_) (Finset.range n)
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω (BrownianGrid.uniformGrid T n i)
  exact MartingaleRandomEvaluation.tendsto_integral_sq_random_evaluation_sub
    hSM hI hS2 hI2 (ae_continuous_stoppedUniformSum hBc T) hIc hτ hτT hlim

end Problem367.BrownianIntegralProcess

end

end OAI
