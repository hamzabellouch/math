import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledAffineComparison

namespace OAI

/-! # Deterministic affine comparison after an exact change of chart -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter
open scoped Topology ENNReal

/-- Two deterministic approximants can be compared under a single law
when their sampled profiles are related by an exact Lipschitz transport. -/
theorem deterministic_distance_tendsto_zero_of_exact_transport
    {X Y Z : Type*} [MeasurableSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (μ : ℕ → ProbabilityMeasure X) (a : ℕ → Y) (b : ℕ → Z)
    (f : ℕ → X → Y) (g : ℕ → X → Z) (H : ℕ → Z → Y)
    {K : ℝ} (hK : 0 < K)
    (hH : ∀ n u v, dist (H n u) (H n v) ≤ K * dist u v)
    (hmatch : ∀ n x, f n x = H n (g n x))
    (hleft : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (a n) (f n x)}) atTop (𝓝 0))
    (hright : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (g n x) (b n)}) atTop (𝓝 0)) :
    Tendsto (fun n => dist (a n) (H n (b n))) atTop (𝓝 0) := by
  apply deterministic_distance_tendsto_zero_of_coupled_profiles μ a (fun n => H n (b n))
    f f hleft
  · intro ε hε
    simpa only [dist_self, Set.ofPred_false, measure_empty,
      show ¬ε ≤ (0 : ℝ) from not_le.mpr hε] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  · intro ε hε
    apply bad_probability_tendsto_zero_of_dist_le (fun n => (μ n : Measure X))
      g (fun n _ => b n) f (fun n _ => H n (b n)) hK
      (fun n x => by rw [hmatch n x]; exact hH n _ _) hright hε

/-- Restriction to a changed compact chart, scalar normalization and the
constant change of center. -/
def transportCompactProfile
    {Z Z' W : Type*} [TopologicalSpace Z] [TopologicalSpace Z']
    [CompactSpace Z] [CompactSpace Z'] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (t : ℝ) (ψ : C(Z, Z')) (c : W) (f : C(Z', W)) : C(Z, W) :=
  t • f.comp ψ + ContinuousMap.const Z c

theorem dist_transportCompactProfile_le
    {Z Z' W : Type*} [TopologicalSpace Z] [TopologicalSpace Z']
    [CompactSpace Z] [CompactSpace Z'] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (t : ℝ) (ψ : C(Z, Z')) (c : W) (f g : C(Z', W)) :
    dist (transportCompactProfile t ψ c f) (transportCompactProfile t ψ c g) ≤
      |t| * dist f g := by
  apply (ContinuousMap.dist_le (mul_nonneg (abs_nonneg _) dist_nonneg)).mpr
  intro z
  change dist (t • f (ψ z) + c) (t • g (ψ z) + c) ≤ _
  rw [dist_add_right, dist_smul₀, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (f.dist_apply_le_dist (g := g) (ψ z)) (abs_nonneg _)

/-- The exact height identity makes the chart transport of an affine
profile affine again, with its center offset explicitly identified. -/
theorem transportCompactProfile_affine
    {Z Z' V W : Type*} [TopologicalSpace Z] [TopologicalSpace Z']
    [CompactSpace Z] [CompactSpace Z']
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (t : ℝ) (ψ : C(Z, Z')) (q : C(Z, V)) (q' : C(Z', V))
    (A : V →L[ℝ] W) (b c : W) (v : V)
    (hheight : ∀ z, t • q' (ψ z) = q z - v) :
    transportCompactProfile t ψ c ((⟨fun z => A (q' z), A.continuous.comp q'.continuous⟩ : C(Z', W)) + ContinuousMap.const Z' b) =
      (⟨fun z => A (q z), A.continuous.comp q.continuous⟩ : C(Z, W)) + ContinuousMap.const Z (t • b + c - A v) := by
  ext z
  change t • (A (q' (ψ z)) + b) + c = A (q z) + (t • b + c - A v)
  rw [smul_add, ← map_smul, hheight, map_sub]
  abel

end PolycyclicRecognition

end

end OAI
