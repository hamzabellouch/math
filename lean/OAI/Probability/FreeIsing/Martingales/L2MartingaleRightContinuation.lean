import OAI.Probability.FreeIsing.Martingales.DominatedMartingaleRightContinuation
import OAI.Probability.FreeIsing.Martingales.StrongMaximal

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.DominatedMartingaleRightContinuation

theorem martingale_rightCont_of_ae_continuous_memLp_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) :
    Martingale M F.rightCont μ := by
  apply martingale_rightCont_of_ae_continuous_dominated hM hc
  intro T
  refine ⟨fun ω => 1 + MartingaleStrongMaximal.maximalSquare M T ω,
    (integrable_const 1).add (MartingaleStrongMaximal.integrable_maximalSquare hM hM2 hc T), ?_⟩
  filter_upwards [MartingaleStrongMaximal.ae_all_sq_le_maximalSquare hM hM2 hc T] with ω hω
  intro t ht
  apply abs_le.mpr
  have hsq := hω t ht
  constructor <;> nlinarith [sq_nonneg (M t ω - 1), sq_nonneg (M t ω + 1)]

theorem martingale_stoppedProcess_rightCont_of_memLp_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ t, MemLp (M t) 2 μ)
    (hprog : IsStronglyProgressive F M)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ) :
    Martingale (stoppedProcess M τ) F.rightCont μ := by
  apply martingale_stoppedProcess_rightCont hM hprog hc _ hτ
  intro T
  refine ⟨fun ω => 1 + MartingaleStrongMaximal.maximalSquare M T ω,
    (integrable_const 1).add (MartingaleStrongMaximal.integrable_maximalSquare hM hM2 hc T), ?_⟩
  filter_upwards [MartingaleStrongMaximal.ae_all_sq_le_maximalSquare hM hM2 hc T] with ω hω
  intro t ht
  apply abs_le.mpr
  have hsq := hω t ht
  constructor <;> nlinarith [sq_nonneg (M t ω - 1), sq_nonneg (M t ω + 1)]

end Problem367.DominatedMartingaleRightContinuation

end

end OAI
