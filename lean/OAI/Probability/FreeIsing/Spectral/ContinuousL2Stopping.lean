import OAI.Probability.FreeIsing.Estimates.ContinuousOptionalStopping
import OAI.Probability.FreeIsing.Martingales.StrongMaximal

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.ContinuousL2Stopping

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}

theorem martingale_stoppedProcess
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P)
    (h2 : ∀ t, MemLp (M t) 2 P) (hp : IsStronglyProgressive F M)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Martingale (stoppedProcess M τ) F P := by
  apply ContinuousOptionalStopping.martingale_stoppedProcess_of_continuous_dominated
    hM hp hc _ hτ
  intro T
  refine ⟨fun ω => 1 + MartingaleStrongMaximal.maximalSquare M T ω,
    (integrable_const 1).add
      (MartingaleStrongMaximal.integrable_maximalSquare hM h2 hc T), ?_⟩
  filter_upwards [MartingaleStrongMaximal.ae_all_sq_le_maximalSquare hM h2 hc T] with ω hω
  intro t ht
  have hs := hω t ht
  nlinarith [sq_abs (M t ω), sq_nonneg (|M t ω| - 1 / 2)]

end Problem367.ContinuousL2Stopping

end

end OAI
