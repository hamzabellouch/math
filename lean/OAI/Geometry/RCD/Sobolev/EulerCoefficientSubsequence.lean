import OAI.Geometry.RCD.Harmonic.HarmonicGrams
import Mathlib.Topology.Sequences

namespace OAI

/-! # A convergent subsequence of the bounded Euler coefficients -/

open Set Metric Filter
open scoped InnerProductSpace Topology

noncomputable section
namespace RegularPointCoordinates

theorem euler_coefficient_subsequence {n : ℕ} (b : ℕ → Euclidean n) (k : ℕ → ℝ)
    {C : ℝ} (hbound : ∀ i, ‖b i‖ + |k i| ≤ C) :
    ∃ t : ℕ → ℕ, StrictMono t ∧ ∃ (L : Euclidean n →L[ℝ] ℝ) (kLimit : ℝ),
      (∀ j, Tendsto (fun i => b (t i) j) atTop (𝓝 (L (EuclideanSpace.single j 1)))) ∧
      Tendsto (k ∘ t) atTop (𝓝 kLimit) := by
  have hmem (i : ℕ) : (b i, k i) ∈ closedBall (0 : Euclidean n × ℝ) C := by
    rw [mem_closedBall, dist_zero_right, Prod.norm_def]
    apply max_le
    · linarith [hbound i, abs_nonneg (k i)]
    · rw [Real.norm_eq_abs]
      linarith [hbound i, norm_nonneg (b i)]
  obtain ⟨z, _hz, t, ht, hconv⟩ := (isCompact_closedBall (0 : Euclidean n × ℝ) C).tendsto_subseq hmem
  let L := innerSL ℝ z.1
  have hfst := (continuous_fst.tendsto z).comp hconv
  have hsnd := (continuous_snd.tendsto z).comp hconv
  refine ⟨t, ht, L, z.2, ?_, ?_⟩
  swap
  · exact hsnd
  intro j
  have hh := (EuclideanSpace.proj j).continuous.tendsto z.1 |>.comp hfst
  change Tendsto (fun i => b (t i) j) atTop (𝓝 (z.1 j)) at hh
  simpa only [L, innerSL_apply_apply, EuclideanSpace.inner_single_right, one_mul,
    conj_trivial] using hh

end RegularPointCoordinates

end

end OAI
