import OAI.Probability.FreeIsing.Brownian.RandomEvaluation
import OAI.Probability.FreeIsing.Martingales.StoppedMartingaleL2
import OAI.Probability.FreeIsing.Stochastic.RandomStoppedSimpleIntegral

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem tendsto_random_stopped_uniformSum
    {B H I : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hBc : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
    (hH : StronglyAdapted F H) {C : ℝ}
    (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hI : Martingale I F P) (hI2 : ∀ t, MemLp (I t) 2 P)
    (hIc : ∀ᵐ ω ∂P, Continuous (fun t => I t ω))
    {T : ℝ≥0}
    (hlim : Tendsto (fun n => ∫ ω,
      (stoppedUniformSum B H T n T ω - I T ω) ^ 2 ∂P) atTop (𝓝 0))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    {t : ℝ≥0} (ht : t ≤ T) :
    Tendsto (fun n => ∫ ω,
      (stoppedUniformSum (stoppedProcess B τ) (stoppedProcess H τ) T n t ω -
        stoppedProcess I τ t ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have h := stopped_uniform_limit_random_evaluation hB hAd hind hBc hH hb
    hI hI2 hIc hlim (StoppedMartingaleL2.measurable_cappedTime hτ t)
    (fun _ => (WithTop.untopA_le (min_le_left _ _)).trans ht)
  change Tendsto (fun n => ∫ ω,
    (stoppedProcess (stoppedUniformSum B H T n) τ t ω -
      stoppedProcess I τ t ω) ^ 2 ∂P) atTop (𝓝 0) at h
  simpa only [RandomStoppedSimpleIntegral.stopped_uniformSum] using h

end Problem367.BrownianIntegralProcess

end

end OAI
