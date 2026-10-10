import OAI.Geometry.RCD.Metric.InnerConstantMeasure
import OAI.Geometry.RCD.Metric.MetricLawCompactness

namespace OAI

/-! # The actual inner-ball laws have the normalized Euclidean subsequential limit -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.metric_inner_law_subsequence {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : K ≤ 0)
    {S ρ : ℝ} (hρ : 0 < ρ) (hρS : ρ < S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hε : Tendsto ε atTop (𝓝 0))
    (hε1 : ∀ k, ε k ≤ 1) (hcurv : ∀ k, -ε k ≤ K*(r k)^2)
    (hlarge : ∀ k, -1 ≤ K*(S*r k)^2)
    (hVm : ∀ k, Measurable (V k))
    (hV : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (V k)) :
    ∃ α : ℕ → ℕ, StrictMono α ∧
      Tendsto (fun k => normalizedBallPushforward (hausdorff n X)
        (p (α k)) (r (α k)) ρ (V (α k)) (hX.finiteOnBounded _ isBounded_ball).ne)
        atTop (𝓝 (euclideanBallProbability n ρ)) := by
  have hS := hρ.trans hρS
  obtain ⟨Q,α,hα,hlim,_,hpos⟩ := hX.metric_law_compactness hn hS p r ε V hr hε hε1 hlarge hVm hV
  obtain ⟨c,hc,he⟩ := hX.metric_limit_measure hn hK hS (p ∘ α) (r ∘ α) (ε ∘ α)
    (V ∘ α) (fun k => hr (α k)) (hε.comp hα.tendsto_atTop) (fun k => hcurv (α k))
    (fun k => hVm (α k)) (fun k => hV (α k))
    (fun k => (hX.finiteOnBounded _ isBounded_ball).ne) hlim hpos
  refine ⟨α,hα,ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_⟩
  intro φ
  have hp (k : ℕ) (t : ℝ) (ht : 0 < t) :
      0 < (hausdorff n X).real (ball (p (α k)) (t*r (α k))) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos ht (hr (α k)))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  have htest := inner_ball_constant_limit_test hρ hρS hc
    (fun k => hr (α k)) (fun k => hV (α k)) (fun k => hVm (α k))
    (fun k => (hX.finiteOnBounded _ isBounded_ball).ne) (fun k => hp k S hS)
    (hε.comp hα.tendsto_atTop) hlim he φ
  simpa only [normalizedBallPushforward_integral _ _ _ _ _ _ (hp _ ρ hρ) (hVm _) φ.continuous,
    euclideanBallProbability_integral hρ] using htest

end RegularPointCoordinates

end

end OAI
