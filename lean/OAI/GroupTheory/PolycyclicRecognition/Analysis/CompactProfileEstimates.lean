import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactSamplingMean
import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearProfilesOnBall

namespace OAI

/-! # The three estimates used in the basepoint argument -/

noncomputable section
namespace PolycyclicRecognition
open MeasureTheory Filter Metric
open scoped Topology

/-- Affine means, vanishing offsets, and deterministic suffix concentration
for the same profiles and ordinary sampling laws. -/
structure CompactProfileEstimates
    {P G N V W L : Type*} [MeasurableSpace N] [Mul N] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [ProperSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (raw : P × G → ℝ → N → C(V, W)) (μ : ℝ → ProbabilityMeasure N)
    (q : V →L[ℝ] W) (A : L → W →L[ℝ] W) (R : ℝ) (B : ℝ → Set N) : Prop where
  mean : ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → StrictMono scale →
    (∀ n, 1 ≤ scale n) → ∀ (p : ℕ → P) (x : ℕ → G),
    ∃ a : ℕ → L, Tendsto (fun n => ∫ k,
      dist ((raw (p n, x n) (scale n) k).restrict (closedBall 0 R))
        (linearBallProfile q (A (a n)) R + ContinuousMap.const _
          (∫ k, raw (p n, x n) (scale n) k 0 ∂(μ (scale n) : Measure N)))
      ∂(μ (scale n) : Measure N)) atTop (𝓝 0)
  zeroMean : ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, ∀ p r, r₀ ≤ r →
    ‖∫ k, raw p r k 0 ∂(μ r : Measure N)‖ ≤ ε
  suffix : ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → StrictMono scale →
    (∀ n, 1 ≤ scale n) → ∀ (p : ℕ → P) (x : ℕ → G) (k : ℕ → N), (∀ n, k n ∈ B (scale n)) → ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => (μ (scale n) : Measure N)
      {z | ε ≤ dist ((raw (p n, x n) (scale n) (z * k n)).restrict (closedBall 0 R))
        ((raw (p n, x n) (scale n) z).restrict (closedBall 0 R))}) atTop (𝓝 0)

end PolycyclicRecognition

end

end OAI
