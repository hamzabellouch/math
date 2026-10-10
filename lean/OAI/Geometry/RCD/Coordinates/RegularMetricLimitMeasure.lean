import OAI.Geometry.RCD.Coordinates.RegularLimitBallMass
import OAI.Geometry.RCD.Metric.MeasurablePointedSequence
import OAI.Geometry.RCD.Metric.MetricBallLawCompactness
import OAI.Geometry.RCD.Metric.ApproximationRestriction

namespace OAI

/-! # The actual normalized volume law on a regular metric limit

The measure is constructed from the original Hausdorff measures and measurable
pointed maps. Its exact interior ball masses require no RCD structure on the
target metric space.
-/

open Set Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [ProperSpace Y]
  {K : ℝ} {n : ℕ}

theorem NoncollapsedRCD.regular_metric_limit_measure
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {o : X} (ho : IsRegular n o)
    {q : Y} {S : ℝ} (hS : 0 < S) (hS5 : S ≤ 5)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hp : Tendsto p atTop (𝓝 o)) (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) 5 (ε k) (V k)) :
    ∃ Q : ProbabilityMeasure Y,
      (∀ᵐ z ∂(Q : Measure Y), z ∈ closedBall q S) ∧
      ∀ (z : Y) (t : ℝ), 0 < t → dist z q+t < S →
        (Q : Measure Y).real (ball z t) = (t/S)^n ∧
        (Q : Measure Y).real (closedBall z t) = (t/S)^n := by
  have hVr k := (hV k).restrict_radius (hr k) hS.le hS5
    (show 0 ≤ ε k from dist_nonneg.trans (hV k).1)
  have h3ε : Tendsto (fun k => 3*ε k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hε.const_mul 3
  obtain ⟨δ,W,hδ,hWm,hW⟩ := measurable_pointed_sequence hS p r _ V hr h3ε hVr
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hδ.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)))
  let ps := fun k => p (k+N)
  let rs := fun k => r (k+N)
  let es := fun k => δ (k+N)
  let Ws := fun k => W (k+N)
  have hfin k : hausdorff n X (ball (ps k) (S*rs k)) ≠ ⊤ :=
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hpos k : 0 < (hausdorff n X).real (ball (ps k) (S*rs k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr _))).ne' (hfin k)
  obtain ⟨Q,α,hα,hlim,-⟩ := metric_ball_law_subsequence hS.le (hausdorff n X)
    ps rs es Ws (fun k => hr _) (fun k => (hN _ (Nat.le_add_left _ _)).le)
    (fun k => hWm _) (fun k => hW _) hfin hpos
  have he0 : Tendsto (fun k => es (α k)) atTop (𝓝 0) :=
    (hδ.comp (tendsto_add_atTop_nat N)).comp hα.tendsto_atTop
  have hr' k : 0 < rs (α k) := hr _
  have hVm' k : Measurable (Ws (α k)) := hWm _
  have hV' k : IsPointedApproximation (ps (α k)) q (rs (α k)) S
      (es (α k)) (Ws (α k)) := hW _
  refine ⟨Q,metric_ball_law_limit_support hS.le (hausdorff n X)
    _ _ _ _ hr' he0 hVm' hV' (fun k => hfin _) (fun k => hpos _) hlim,?_⟩
  intro z t ht hzt
  exact hX.regular_limit_ball_mass hn ho hS ht hzt _ _ _ _
    ((hp.comp (tendsto_add_atTop_nat N)).comp hα.tendsto_atTop) hr'
    ((hr0.comp (tendsto_add_atTop_nat N)).comp hα.tendsto_atTop)
    he0 hVm' hV' (fun k => hfin _) hlim

end RegularPointCoordinates

end

end OAI
