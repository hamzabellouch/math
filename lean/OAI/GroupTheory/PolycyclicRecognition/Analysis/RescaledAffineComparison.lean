import OAI.GroupTheory.PolycyclicRecognition.Analysis.DeterministicProbabilityComparison
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteAffineSelection
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! # Deterministic comparison through a change of scale

Two ordinary sampling laws need not agree. Their mixed comparison and the
exact change of coordinates suffice to compare the deterministic affine
approximations. Finite separation then identifies their linear parts.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem bad_probability_tendsto_zero_of_dist_le
    {X Y Z : Type*} [MeasurableSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (μ : ℕ → Measure X) (f g : ℕ → X → Y) (u v : ℕ → X → Z)
    {K : ℝ} (hK : 0 < K)
    (hbound : ∀ n x, dist (u n x) (v n x) ≤ K * dist (f n x) (g n x))
    (hp : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ n {x | ε ≤ dist (f n x) (g n x)}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => μ n {x | ε ≤ dist (u n x) (v n x)}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞)) tendsto_const_nhds
    (hp (ε / K) (div_pos hε hK)) (fun _ => zero_le)
  intro n
  apply measure_mono
  intro x hx
  exact (div_le_iff₀ hK).mpr (by simpa only [mul_comm] using hx.trans (hbound n x))

/-- A mixed sampling comparison transports deterministic approximants
through any uniformly Lipschitz exact change of coordinates. -/
theorem deterministic_distance_tendsto_zero_of_rescaled_profiles
    {X Y : Type*} [MeasurableSpace X] [PseudoMetricSpace Y]
    (μ ν : ℕ → ProbabilityMeasure X) (a b : ℕ → Y)
    (f g : ℕ → X → Y) (H : ℕ → Y → Y) {K : ℝ} (hK : 0 < K)
    (hH : ∀ n u v, dist (H n u) (H n v) ≤ K * dist u v)
    (hmatch : ∀ n x, f n x = H n (g n x))
    (hleft : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (a n) (f n x)}) atTop (𝓝 0))
    (hpair : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X).prod (ν n : Measure X)
        {p | ε ≤ dist (f n p.1) (f n p.2)}) atTop (𝓝 0))
    (hright : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (ν n : Measure X) {x | ε ≤ dist (g n x) (b n)}) atTop (𝓝 0)) :
    Tendsto (fun n => dist (a n) (H n (b n))) atTop (𝓝 0) := by
  let ρ n : ProbabilityMeasure (X × X) :=
    ⟨(μ n : Measure X).prod (ν n : Measure X), inferInstance⟩
  apply deterministic_distance_tendsto_zero_of_coupled_profiles ρ a (fun n => H n (b n))
    (fun n p => f n p.1) (fun n p => f n p.2)
  · intro ε hε
    change Tendsto (fun n => (μ n : Measure X).prod (ν n : Measure X)
      {p | ε ≤ dist (a n) (f n p.1)}) atTop (𝓝 0)
    have he n : {p : X × X | ε ≤ dist (a n) (f n p.1)} =
        {x | ε ≤ dist (a n) (f n x)} ×ˢ univ := by ext p; simp
    simpa only [he, Measure.prod_prod, measure_univ, mul_one] using hleft ε hε
  · exact hpair
  · intro ε hε
    change Tendsto (fun n => (μ n : Measure X).prod (ν n : Measure X)
      {p | ε ≤ dist (f n p.2) (H n (b n))}) atTop (𝓝 0)
    have hh := bad_probability_tendsto_zero_of_dist_le
      (fun n => (ν n : Measure X)) g (fun n _ => b n)
      f (fun n _ => H n (b n)) hK
      (fun n x => by rw [hmatch n x]; exact hH n _ _) hright hε
    have he n : {p : X × X | ε ≤ dist (f n p.2) (H n (b n))} =
        univ ×ˢ {x | ε ≤ dist (f n x) (H n (b n))} := by ext p; simp
    simpa only [he, Measure.prod_prod, measure_univ, one_mul] using hh

/-- The operator on compact profiles induced by a change of chart. -/
def rescaleCompactProfile {Z W : Type*} [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (t : ℝ) (φ : C(Z, Z)) (f : C(Z, W)) : C(Z, W) := t • f.comp φ

theorem dist_rescaleCompactProfile_le
    {Z W : Type*} [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (t : ℝ) (φ : C(Z, Z)) (f g : C(Z, W)) :
    dist (rescaleCompactProfile t φ f) (rescaleCompactProfile t φ g) ≤
      |t| * dist f g := by
  apply (ContinuousMap.dist_le (mul_nonneg (abs_nonneg _) dist_nonneg)).mpr
  intro z
  change dist (t • f (φ z)) (t • g (φ z)) ≤ _
  rw [dist_smul₀, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (f.dist_apply_le_dist (g := g) (φ z)) (abs_nonneg _)

/-- A linear profile transforms exactly; only its constant offset changes. -/
theorem rescaleCompactProfile_affine
    {Z W : Type*} [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (t : ℝ) (φ : C(Z, Z)) (A : C(Z, W)) (b : W)
    (hA : ∀ z, t • A (φ z) = A z) :
    rescaleCompactProfile t φ (A + ContinuousMap.const Z b) =
      A + ContinuousMap.const Z (t • b) := by
  ext z
  change t • (A (φ z) + b) = A z + t • b
  rw [smul_add, hA]

/-- Vanishing affine discrepancy identifies finite labels and their offsets. -/
theorem affine_labels_and_offsets_of_distance_tendsto_zero
    {Z W L : Type*} [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [Fintype L] [Nonempty L]
    (A : L → C(Z, W)) (hA : Function.Injective A)
    (z₀ : Z) (hzero : ∀ a, A a z₀ = 0)
    (a a' : ℕ → L) (b b' : ℕ → W)
    (hd : Tendsto (fun n => dist (A (a n) + ContinuousMap.const Z (b n))
      (A (a' n) + ContinuousMap.const Z (b' n))) atTop (𝓝 0)) :
    (∀ᶠ n in atTop, a n = a' n) ∧
      Tendsto (fun n => dist (b n) (b' n)) atTop (𝓝 0) := by
  obtain ⟨ε, hε, hsep⟩ := exists_finite_affine_label_separation A hA z₀ hzero
  constructor
  · filter_upwards [hd.eventually (gt_mem_nhds hε)] with n hn
    exact hsep _ _ _ _ hn
  · apply squeeze_zero (fun _ => dist_nonneg) _ hd
    intro n
    simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply, hzero, zero_add] using
      (A (a n) + ContinuousMap.const Z (b n)).dist_apply_le_dist
        (g := A (a' n) + ContinuousMap.const Z (b' n)) z₀

end PolycyclicRecognition

end

end OAI
