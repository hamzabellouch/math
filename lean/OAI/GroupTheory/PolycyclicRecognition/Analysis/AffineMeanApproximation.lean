import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactSetMeanApproximation
import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffineProfileConcentration

namespace OAI

/-! # Deterministic affine profiles and their mean-normalized offsets -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set Metric
open scoped Topology

/-- No point-mass choice is necessary: the first-moment argument selects
an actual affine profile whenever the independent and affine errors vanish. -/
theorem exists_affine_mean_approximation
    {S Z W L : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace Z] [CompactSpace Z] [NormedAddCommGroup W] [Nonempty L]
    (F : S → C(Z, W)) (hF : Continuous F) (A : L → C(Z, W))
    (μ : ℕ → ProbabilityMeasure S)
    (hpair : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure S).prod (μ n : Measure S) {p | ε ≤ dist (F p.1) (F p.2)})
        atTop (𝓝 0))
    (haffine : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure S) {x | ε ≤ infDist (F x) (affineProfileClass A)})
        atTop (𝓝 0)) :
    ∃ (a : ℕ → L) (b : ℕ → W), Tendsto (fun n =>
      ∫ x, dist (F x) (A (a n) + ContinuousMap.const Z (b n)) ∂(μ n : Measure S))
      atTop (𝓝 0) := by
  obtain ⟨p, hp, hm⟩ := exists_set_mean_approximation F hF (affineProfileClass A)
    (affineProfileClass_nonempty A) μ
    (pair_mean_tendsto_zero_of_probability F hF μ hpair)
    (set_distance_mean_tendsto_zero_of_probability F hF _ μ haffine)
  have hx n : ∃ a b, ∀ z, p n z = A a z + b := hp n
  choose a b hab using hx
  have heq n : p n = A (a n) + ContinuousMap.const Z (b n) := by
    ext z
    exact hab n z
  exact ⟨a, b, by simpa only [heq] using hm⟩

/-- Pointwise cancellation controls the distance between affine offsets. -/
theorem affine_profiles_offset_dist_le
    {Z W : Type*} [TopologicalSpace Z] [CompactSpace Z] [NormedAddCommGroup W]
    (A : C(Z, W)) (b c : W) :
    dist (A + ContinuousMap.const Z b) (A + ContinuousMap.const Z c) ≤ dist b c := by
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro z
  simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, dist_add_left]
  exact le_rfl

/-- Evaluation and the norm integral inequality control the change of offset. -/
theorem mean_affine_offset_dist_le
    {S Z W : Type*} [TopologicalSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S] [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (F : S → C(Z, W)) (hF : Continuous F) (A : C(Z, W))
    (z₀ : Z) (hA : A z₀ = 0) (b : W) (μ : ProbabilityMeasure S) :
    dist b (∫ y, F y z₀ ∂(μ : Measure S)) ≤
      ∫ x, dist (F x) (A + ContinuousMap.const Z b) ∂(μ : Measure S) := by
  have heval : Continuous (fun y => F y z₀) := (continuous_eval_const z₀).comp hF
  have hev : Integrable (fun y => F y z₀) (μ : Measure S) :=
    heval.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hid : (∫ y, F y z₀ - b ∂(μ : Measure S)) = (∫ y, F y z₀ ∂(μ : Measure S)) - b := by
    rw [integral_sub hev (integrable_const b)]
    simp
  calc
    _ = ‖(∫ y, F y z₀ ∂(μ : Measure S)) - b‖ := by rw [dist_comm, dist_eq_norm]
    _ ≤ ∫ y, ‖F y z₀ - b‖ ∂(μ : Measure S) := by
      rw [← hid]
      exact norm_integral_le_integral_norm _
    _ ≤ _ := by
      have hi : Integrable (fun y => ‖F y z₀ - b‖) (μ : Measure S) :=
        (heval.sub continuous_const).norm.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hj : Integrable (fun y => dist (F y) (A + ContinuousMap.const Z b))
          (μ : Measure S) :=
        (hF.dist continuous_const).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      apply integral_mono hi hj
      intro y
      change ‖F y z₀ - b‖ ≤ dist (F y) (A + ContinuousMap.const Z b)
      have hh := (F y).dist_apply_le_dist (g := A + ContinuousMap.const Z b) z₀
      simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply, hA,
        zero_add, dist_eq_norm] using hh

/-- Replacing an approximate affine offset by the mean value at the
identity increases the mean error by at most a factor of two. -/
theorem mean_normalized_affine_error_le
    {S Z W : Type*} [TopologicalSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (F : S → C(Z, W)) (hF : Continuous F) (A : C(Z, W))
    (z₀ : Z) (hA : A z₀ = 0) (b : W) (μ : ProbabilityMeasure S) :
    (∫ x, dist (F x) (A + ContinuousMap.const Z
      (∫ y, F y z₀ ∂(μ : Measure S))) ∂(μ : Measure S)) ≤
      2 * ∫ x, dist (F x) (A + ContinuousMap.const Z b) ∂(μ : Measure S) := by
  let c := ∫ y, F y z₀ ∂(μ : Measure S)
  have hoff := mean_affine_offset_dist_le F hF A z₀ hA b μ
  have hc := affine_profiles_offset_dist_le A b c
  have hi (g : S → ℝ) (hg : Continuous g) : Integrable g (μ : Measure S) :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ x, dist (F x) (A + ContinuousMap.const Z b) + dist b c ∂(μ : Measure S) := by
      apply integral_mono (hi _ (hF.dist continuous_const))
        (hi _ ((hF.dist continuous_const).add continuous_const))
      intro x
      change dist (F x) (A + ContinuousMap.const Z c) ≤
        dist (F x) (A + ContinuousMap.const Z b) + dist b c
      exact (dist_triangle (F x) (A + ContinuousMap.const Z b)
        (A + ContinuousMap.const Z c)).trans (add_le_add le_rfl hc)
    _ = (∫ x, dist (F x) (A + ContinuousMap.const Z b) ∂(μ : Measure S)) + dist b c := by
      rw [integral_add (hi _ (hF.dist continuous_const)) (integrable_const _)]
      simp
    _ ≤ _ := by linarith

/-- The deterministic offset is exactly the mean height at the identity. -/
theorem exists_mean_normalized_affine_approximation
    {S Z W L : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [Nonempty L]
    (F : S → C(Z, W)) (hF : Continuous F) (A : L → C(Z, W))
    (z₀ : Z) (hA : ∀ a, A a z₀ = 0) (μ : ℕ → ProbabilityMeasure S)
    (hpair : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure S).prod (μ n : Measure S) {p | ε ≤ dist (F p.1) (F p.2)})
        atTop (𝓝 0))
    (haffine : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure S) {x | ε ≤ infDist (F x) (affineProfileClass A)})
        atTop (𝓝 0)) :
    ∃ a : ℕ → L, Tendsto (fun n => ∫ x,
      dist (F x) (A (a n) + ContinuousMap.const Z (∫ y, F y z₀ ∂(μ n : Measure S)))
        ∂(μ n : Measure S)) atTop (𝓝 0) := by
  obtain ⟨a, b, hab⟩ := exists_affine_mean_approximation F hF A μ hpair haffine
  refine ⟨a, squeeze_zero (fun _ => integral_nonneg (fun _ => dist_nonneg))
    (fun n => mean_normalized_affine_error_le F hF (A (a n)) z₀ (hA (a n)) (b n) (μ n)) ?_⟩
  simpa only [mul_zero] using hab.const_mul 2

end PolycyclicRecognition

end

end OAI
