import OAI.Probability.FreeIsing.Brownian.ContinuousIntegral
import OAI.Probability.FreeIsing.Brownian.IntegralCompensator

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem exists_continuous_integral_with_compensator
    {B H : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hBc : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
    (hH : StronglyAdapted F H) (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C) (T : ℝ≥0) :
    ∃ M Q : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F M ∧ IsStronglyPredictable F Q ∧
      Martingale M F P ∧ (∀ t, MemLp (M t) 2 P) ∧
      (∀ᵐ ω ∂P, Continuous (fun t => M t ω)) ∧ M 0 =ᵐ[P] 0 ∧
      (∀ᵐ ω ∂P, Continuous (fun t => Q t ω) ∧ Monotone (fun t => Q t ω)) ∧
      Q 0 =ᵐ[P] 0 ∧ (∀ t, Integrable (Q t) P) ∧
      (∀ᵐ ω ∂P, ∀ t, Q t ω =
        ∫ s in (0 : ℝ)..min (t : ℝ) T, (H s.toNNReal ω) ^ 2) ∧
      Martingale (fun t ω => (M t ω) ^ 2 - Q t ω) F P ∧
      (∀ᵐ ω ∂P, ∀ s t, |Q t ω - Q s ω| ≤ C ^ 2 * |(t : ℝ) - s|) ∧
      (∀ t, Tendsto (fun n => ∫ ω,
        (stoppedUniformSum B H T n t ω - M t ω) ^ 2 ∂P) atTop (𝓝 0)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨M, hp, hM, hMc, hM2, hMzero, _, _, _, hlim⟩ :=
    exists_continuous_stopped_uniform_integral hB hAd hind hBc hH hc hC hb T
  let Q := PredictableMesh.repair (SelectedCompensator.selected H T)
  have hQp : IsStronglyPredictable F Q :=
    PredictableMesh.repair_isStronglyPredictable
      (SelectedCompensator.selected_stronglyAdapted hH T)
  have hQeq : ∀ᵐ ω ∂P, ∀ t, Q t ω = SelectedCompensator.selected H T t ω := by
    filter_upwards [SelectedCompensator.ae_continuous_selected hc T] with ω hω
    intro t
    exact PredictableMesh.repair_eq_of_continuousOn (T := t) hω.continuousOn le_rfl
  have hcomp := stopped_uniform_limit_compensatedSquare
    hB hAd hind hH hc hC hb T hM.stronglyAdapted hM2 hlim
  refine ⟨M, Q, hp, hQp, hM, hM2, hMc, hMzero, ?_, ?_, ?_, ?_, ?_, ?_, hlim⟩
  · filter_upwards [hQeq, SelectedCompensator.ae_continuous_selected hc T, hc]
      with ω heq hcont hcω
    constructor
    · exact hcont.congr (fun t => (heq t).symm)
    · intro s t hst
      change Q s ω ≤ Q t ω
      rw [heq s, heq t]
      exact SelectedCompensator.selected_monotone_of_continuous hcω T hst
  · filter_upwards [hQeq] with ω hω
    simp only [hω 0, SelectedCompensator.selected_zero, Pi.zero_apply]
  · intro t
    apply ((SelectedCompensator.selected_memLp hH hc hC hb T t 1).integrable le_rfl).congr
    filter_upwards [hQeq] with ω hω
    exact (hω t).symm
  · filter_upwards [hQeq, SelectedCompensator.ae_selected_eq_integral hc T] with ω heq hω
    intro t
    exact (heq t).trans (hω t)
  · apply hcomp.congr (fun t => ((hM.stronglyAdapted t).pow 2).sub (hQp.stronglyAdapted t))
    intro t
    filter_upwards [hQeq] with ω hω
    change M t ω ^ 2 - SelectedCompensator.selected H T t ω = M t ω ^ 2 - Q t ω
    rw [hω t]
  · filter_upwards [hQeq, hc, hb] with ω heq hcω hbω
    intro s t
    rw [heq s, heq t]
    exact SelectedCompensator.abs_selected_sub_le hcω hC hbω T s t

end Problem367.BrownianIntegralProcess

end

end OAI
