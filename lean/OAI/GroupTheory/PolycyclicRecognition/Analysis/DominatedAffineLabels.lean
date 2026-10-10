import OAI.GroupTheory.PolycyclicRecognition.Analysis.DominatedAffineComparison
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BasepointAffineSeparation

namespace OAI

/-! # Finite labels and normalized center error from dominated sampling -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

/-- The density bound, the two concentration statements and the exact chart
identities give both eventual equality of labels and a vanishing center
error. No height conclusion is assumed. -/
theorem affine_labels_center_error_of_dominated_transport
    {X V W L : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype L] [Nonempty L]
    (q : V →L[ℝ] W) (hq : Function.Surjective q)
    (A : L → W →L[ℝ] W) (hA : Function.Injective A)
    {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (ξ μ ν : ℕ → ProbabilityMeasure X)
    (a a' : ℕ → L) (b b' c v : ℕ → W) {t : ℝ} (ht : 0 < t)
    (φ : ℕ → C(closedBall (0 : V) R, closedBall (0 : V) S))
    (ψ : ℕ → X → X) (m : ℕ → X → X → X)
    (f : ℕ → X → C(closedBall (0 : V) R, W))
    (g : ℕ → X → C(closedBall (0 : V) S, W))
    (hheight : ∀ᶠ n in atTop, ∀ z, t • q (φ n z) = q z - v n)
    (hmatch : ∀ᶠ n in atTop, ∀ x,
      f n x = transportCompactProfile t (φ n) (c n) (g n (ψ n x)))
    {D : ℝ≥0∞} (hD : D ≠ ∞)
    (hmeas : ∀ n ε, MeasurableSet {x | ε ≤ dist (g n x)
      (linearBallProfile q (A (a' n)) S + ContinuousMap.const _ (b' n))})
    (hdom : ∀ᶠ n in atTop, ∀ U : Set X, MeasurableSet U →
      (ξ n : Measure X) (ψ n ⁻¹' U) ≤ D *
        (μ n : Measure X).prod (ν n : Measure X) {p | m n p.1 p.2 ∈ U})
    (hsource : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (ξ n : Measure X)
      {x | ε ≤ dist (linearBallProfile q (A (a n)) R + ContinuousMap.const _ (b n))
        (f n x)}) atTop (𝓝 0))
    (hordinary : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n : Measure X)
      {x | ε ≤ dist (g n x)
        (linearBallProfile q (A (a' n)) S + ContinuousMap.const _ (b' n))})
      atTop (𝓝 0))
    (hsuffix : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X).prod (ν n : Measure X)
        {p | ε ≤ dist (g n (m n p.1 p.2)) (g n p.1)}) atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0)) (hb' : Tendsto b' atTop (𝓝 0)) :
    (∀ᶠ n in atTop, a n = a' n) ∧
      Tendsto (fun n => c n - A (a' n) (v n)) atTop (𝓝 0) := by
  have hd := deterministic_distance_tendsto_zero_of_dominated_transport ξ μ ν
    (fun n => linearBallProfile q (A (a n)) R + ContinuousMap.const _ (b n))
    (fun n => linearBallProfile q (A (a' n)) S + ContinuousMap.const _ (b' n))
    f g ψ m (fun n => transportCompactProfile t (φ n) (c n)) ht
    (fun n u w => by
      simpa only [abs_of_pos ht] using dist_transportCompactProfile_le t (φ n) (c n) u w)
    hmatch hD hmeas hdom hsource hordinary hsuffix
  obtain ⟨heq, hoff⟩ := affine_labels_offsets_of_chart_transport q hq A hA hR hS
    a a' b b' c v (fun _ => t) φ hheight hd
  exact ⟨heq, center_error_tendsto_zero_of_offsets A a' b b' c v t hb hb' hoff⟩

end PolycyclicRecognition

end

end OAI
