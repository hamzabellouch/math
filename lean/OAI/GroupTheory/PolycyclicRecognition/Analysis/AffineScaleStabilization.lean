import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledAffineComparison
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactSamplingMean

namespace OAI

/-! # Stabilization of affine approximations across comparable scales -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

/-- Mixed concentration and the exact chart transition stabilize the finite
labels. The offsets are compared in the physical source-scale normalization. -/
theorem affine_scale_labels_and_offsets
    {X Z W L : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype L] [Nonempty L]
    (μ ν : ℕ → ProbabilityMeasure X) (C D : ℕ → Set X)
    (hC : ∀ n, IsCompact (C n)) (hD : ∀ n, IsCompact (D n))
    (hμ : ∀ n, ∀ᵐ x ∂(μ n : Measure X), x ∈ C n)
    (hν : ∀ n, ∀ᵐ x ∂(ν n : Measure X), x ∈ D n)
    (f g : ℕ → X → C(Z, W)) (hf : ∀ n, Continuous (f n)) (hg : ∀ n, Continuous (g n))
    (t : ℕ → ℝ) (φ : ℕ → C(Z, Z)) {K : ℝ} (hK : 0 < K)
    (ht : ∀ n, |t n| ≤ K)
    (hmatch : ∀ n x, f n x = rescaleCompactProfile (t n) (φ n) (g n x))
    (A : L → C(Z, W)) (hA : Function.Injective A)
    (z₀ : Z) (hzero : ∀ a, A a z₀ = 0)
    (htransition : ∀ n a z, t n • A a (φ n z) = A a z)
    (a a' : ℕ → L) (b b' : ℕ → W)
    (hleft : Tendsto (fun n => ∫ x, dist (f n x)
      (A (a n) + ContinuousMap.const Z (b n)) ∂(μ n : Measure X)) atTop (𝓝 0))
    (hright : Tendsto (fun n => ∫ x, dist (g n x)
      (A (a' n) + ContinuousMap.const Z (b' n)) ∂(ν n : Measure X)) atTop (𝓝 0))
    (hpair : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X).prod (ν n : Measure X)
        {p | ε ≤ dist (f n p.1) (f n p.2)}) atTop (𝓝 0)) :
    (∀ᶠ n in atTop, a n = a' n) ∧
      Tendsto (fun n => dist (b n) (t n • b' n)) atTop (𝓝 0) := by
  have hd := deterministic_distance_tendsto_zero_of_rescaled_profiles μ ν
    (fun n => A (a n) + ContinuousMap.const Z (b n))
    (fun n => A (a' n) + ContinuousMap.const Z (b' n)) f g
    (fun n => rescaleCompactProfile (t n) (φ n)) hK
    (fun n u v => (dist_rescaleCompactProfile_le _ _ _ _).trans
      (mul_le_mul_of_nonneg_right (ht n) dist_nonneg)) hmatch
    (fun ε hε => by
      simpa only [dist_comm] using
        compact_profile_probability_of_mean μ C hC hμ f hf _ hleft hε)
    hpair
    (fun ε hε => compact_profile_probability_of_mean ν D hD hν g hg _ hright hε)
  have he n := rescaleCompactProfile_affine (t n) (φ n) (A (a' n)) (b' n)
    (htransition n (a' n))
  simp_rw [he] at hd
  exact affine_labels_and_offsets_of_distance_tendsto_zero A hA z₀ hzero a a' b _ hd

end PolycyclicRecognition

end

end OAI
