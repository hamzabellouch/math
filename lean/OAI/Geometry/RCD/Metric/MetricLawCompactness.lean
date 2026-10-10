import OAI.Geometry.RCD.Metric.PointedProbabilityCompactness
import OAI.Geometry.RCD.Metric.PointedInteriorBallMass

namespace OAI

/-! # Compactness and full interior support of the actual RCD metric laws

The limiting probability measure has full interior support without a
measured-coordinate hypothesis.
-/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.metric_law_compactness {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {S : ℝ} (hS : 0 < S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hε : Tendsto ε atTop (𝓝 0))
    (hε1 : ∀ k, ε k ≤ 1) (hcurv : ∀ k, -1 ≤ K*(S*r k)^2)
    (hVm : ∀ k, Measurable (V k))
    (hV : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (V k)) :
    ∃ Q : ProbabilityMeasure (Euclidean n), ∃ α : ℕ → ℕ, StrictMono α ∧
      Tendsto (fun k => normalizedBallPushforward (hausdorff n X)
        (p (α k)) (r (α k)) S (V (α k)) (hX.finiteOnBounded _ isBounded_ball).ne)
          atTop (𝓝 Q) ∧
      (∀ᵐ z ∂(Q : Measure (Euclidean n)), z ∈ closedBall 0 S) ∧
      ∀ z ∈ ball (0 : Euclidean n) S, ∀ b : ℝ, 0 < b →
        0 < (Q : Measure (Euclidean n)).real (ball z b) := by
  let hfin (k : ℕ) : hausdorff n X (ball (p k) (S*r k)) ≠ ⊤ :=
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hpos (k : ℕ) : 0 < (hausdorff n X).real (ball (p k) (S*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne' (hfin k)
  obtain ⟨Q,α,hα,hlim,_⟩ := pointed_probability_subsequence hS.le (hausdorff n X)
    p r ε V hr hε1 hVm hV hfin hpos
  have hε' := hε.comp hα.tendsto_atTop
  refine ⟨Q,α,hα,hlim,?_,?_⟩
  · exact pointed_probability_limit_support hS.le (hausdorff n X)
      (p ∘ α) (r ∘ α) (ε ∘ α) (V ∘ α) (fun k => hr (α k)) hε'
      (fun k => hVm (α k)) (fun k => hV (α k)) (fun k => hfin (α k))
      (fun k => hpos (α k)) hlim
  · intro z hz b hb
    exact hX.metric_probability_limit_positive hn hS (p ∘ α) (r ∘ α) (ε ∘ α)
      (V ∘ α) (fun k => hr (α k)) hε' (Eventually.of_forall (fun k => hcurv (α k)))
      (fun k => hVm (α k)) (fun k => hV (α k)) (fun k => hfin (α k)) hlim hz hb

end RegularPointCoordinates

end

end OAI
