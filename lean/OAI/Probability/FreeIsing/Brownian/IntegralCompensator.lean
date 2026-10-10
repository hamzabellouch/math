import OAI.Probability.FreeIsing.Brownian.IntegralProcess
import OAI.Probability.FreeIsing.Estimates.CompensatedSquareLimit
import OAI.Probability.FreeIsing.Stochastic.SelectedCompensator
import OAI.Probability.FreeIsing.Stochastic.StoppedBrownianSquare

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem stopped_uniform_limit_compensatedSquare
    {B H M : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (T : ℝ≥0) (hM : StronglyAdapted F M) (hM2 : ∀ t, MemLp (M t) 2 P)
    (hlim : ∀ t, Tendsto (fun n => ∫ ω,
      (stoppedUniformSum B H T n t ω - M t ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Martingale (fun t ω => (M t ω) ^ 2 - SelectedCompensator.selected H T t ω) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P := by
    apply MemLp.of_bound hH.stronglyMeasurable.aestronglyMeasurable C
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hS2 (n : ℕ) (t : ℝ≥0) : MemLp (stoppedUniformSum B H T n t) 2 P :=
    BrownianFiltration.stopped_predictable_sum_memLp_two hB hind
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun i => H (BrownianGrid.uniformGrid T n i)) (fun i => hH _) (fun i => hH2 _)
      (Finset.range n) t
  have hfinite (n : ℕ) : Martingale (fun t ω =>
      (stoppedUniformSum B H T n t ω) ^ 2 - SelectedCompensator.squareSum H T n t ω) F P := by
    have h := StoppedBrownianSquare.stopped_predictable_sum_square_martingale hB hAd hind
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun i => H (BrownianGrid.uniformGrid T n i)) (fun i => hH _) (fun _ => C)
      (fun i => hb.mono (fun ω hω => by simpa only [Real.norm_eq_abs] using hω _)) n
    simpa only [stoppedUniformSum, SelectedCompensator.squareSum, mul_comm] using h
  apply CompensatedSquareLimit.martingale_compensatedSquare_of_limits (l := atTop)
    hS2 (fun n t => (SelectedCompensator.squareSum_memLp hH hC hb T t n 1).integrable le_rfl)
    hfinite hM hM2 (SelectedCompensator.selected_stronglyAdapted hH T)
    (fun t => (SelectedCompensator.selected_memLp hH hc hC hb T t 1).integrable le_rfl)
  · intro t
    exact CompensatedSquareLimit.tendsto_eLpNorm_two_of_meanSquare
      (fun n => hS2 n t) (hM2 t) (hlim t)
  · intro t
    exact SelectedCompensator.tendsto_squareSum_L1_selected
      (fun s => hH.stronglyMeasurable.aestronglyMeasurable) hc hC hb T t

theorem exists_stopped_uniform_integral_compensatedSquare
    {B H : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C) (T : ℝ≥0) :
    ∃ M Q : ℝ≥0 → Ω → ℝ, Martingale M F P ∧
      (∀ t, MemLp (M t) 2 P) ∧ StronglyAdapted F Q ∧
      (∀ᵐ ω ∂P, Continuous (fun t => Q t ω)) ∧
      (∀ᵐ ω ∂P, ∀ t, Q t ω =
        ∫ s in (0 : ℝ)..min (t : ℝ) T, (H s.toNNReal ω) ^ 2) ∧
      Martingale (fun t ω => (M t ω) ^ 2 - Q t ω) F P ∧
      (∀ t, Tendsto (fun n => ∫ ω,
        (stoppedUniformSum B H T n t ω - M t ω) ^ 2 ∂P) atTop (𝓝 0)) := by
  obtain ⟨M, hM, hM2, _, _, _, hlim⟩ :=
    exists_stopped_uniform_integral_process hB hAd hind hH hc hC hb T
  exact ⟨M, SelectedCompensator.selected H T, hM, hM2,
    SelectedCompensator.selected_stronglyAdapted hH T,
    SelectedCompensator.ae_continuous_selected hc T,
    SelectedCompensator.ae_selected_eq_integral hc T,
    stopped_uniform_limit_compensatedSquare hB hAd hind hH hc hC hb T hM.stronglyAdapted hM2 hlim,
    hlim⟩

end Problem367.BrownianIntegralProcess

end

end OAI
