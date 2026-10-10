import OAI.GroupTheory.PolycyclicRecognition.Algebra.OccupationWeakLimit
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace OAI

/-! # Passing vanishing profile errors to every supported limit -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Metric Set
open scoped Topology

/-- Uniformly convergent observables can be integrated against a weakly
convergent family of probabilities. Both vary in this statement. -/
theorem integral_tendsto_of_uniformly_and_weakly
    {X ι : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {l : Filter ι}
    (μs : ι → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs l (𝓝 μ)) (fs : ι → C(X, ℝ)) (f : C(X, ℝ))
    (hf : TendstoUniformly (fun i x => fs i x) f l) :
    Tendsto (fun i => ∫ x, fs i x ∂(μs i : Measure X)) l
      (𝓝 (∫ x, f x ∂(μ : Measure X))) := by
  have herr : Tendsto (fun i => ∫ x, (fs i x - f x) ∂(μs i : Measure X)) l (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp hf) (ε / 2) (half_pos hε)] with i hi
    have hb := norm_integral_le_of_norm_le_const (μ := (μs i : Measure X))
      (f := fun x => fs i x - f x) (C := ε / 2)
      (Eventually.of_forall (fun x => by simpa only [dist_eq_norm, norm_sub_rev] using (hi x).le))
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] at hb
    simpa only [dist_zero_right] using hb.trans_lt (half_lt_self hε)
  have hfixed := (ProbabilityMeasure.continuous_integral_continuousMap f).tendsto μ |>.comp hμ
  have hsum := herr.add hfixed
  simp only [zero_add] at hsum
  apply hsum.congr
  intro i
  rw [integral_sub ((fs i).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  exact sub_add_cancel _ _

/-- A continuous nonnegative error with vanishing expectations vanishes at
every point in the support of the weak limit. -/
theorem zero_on_support_of_uniformly_vanishing_integrals
    {X ι : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {l : Filter ι} [l.NeBot]
    (μs : ι → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs l (𝓝 μ)) (fs : ι → C(X, ℝ)) (f : C(X, ℝ))
    (hf : TendstoUniformly (fun i x => fs i x) f l)
    (hpos : ∀ x, 0 ≤ f x)
    (hzero : Tendsto (fun i => ∫ x, fs i x ∂(μs i : Measure X)) l (𝓝 0))
    {x : X} (hx : x ∈ (μ : Measure X).support) : f x = 0 := by
  have hint : ∫ x, f x ∂(μ : Measure X) = 0 :=
    tendsto_nhds_unique (integral_tendsto_of_uniformly_and_weakly μs μ hμ fs f hf) hzero
  have hae : f =ᵐ[(μ : Measure X)] 0 :=
    (integral_eq_zero_iff_of_nonneg hpos (f.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))).mp hint
  exact (μ : Measure X).support_subset_of_isClosed
    (isClosed_eq f.continuous continuous_const) hae hx

/-- Apply the preceding result to distance from a nonempty closed convex
constraint set. The conclusion holds on the support, not just almost surely. -/
theorem mem_on_support_of_uniformly_vanishing_distance
    {X W ι : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [PseudoMetricSpace W]
    {l : Filter ι} [l.NeBot]
    (μs : ι → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs l (𝓝 μ)) (vs : ι → C(X, W)) (v : C(X, W))
    (hv : TendstoUniformly (fun i x => vs i x) v l)
    {S : Set W} (hS : IsClosed S) (hne : S.Nonempty)
    (hzero : Tendsto (fun i => ∫ x, infDist (vs i x) S ∂(μs i : Measure X)) l (𝓝 0))
    {x : X} (hx : x ∈ (μ : Measure X).support) : v x ∈ S := by
  apply (hS.mem_iff_infDist_zero hne).mpr
  let fs : ι → C(X, ℝ) := fun i => ⟨fun x => infDist (vs i x) S,
    (continuous_infDist_pt S).comp (vs i).continuous⟩
  let f : C(X, ℝ) := ⟨fun x => infDist (v x) S,
    (continuous_infDist_pt S).comp v.continuous⟩
  have hf : TendstoUniformly (fun i x => fs i x) f l := by
    rw [Metric.tendstoUniformly_iff] at hv ⊢
    intro ε hε
    filter_upwards [hv ε hε] with i hi
    intro y
    exact (lipschitz_infDist_pt S).dist_le_mul (v y) (vs i y) |>.trans_lt (by simpa using hi y)
  exact zero_on_support_of_uniformly_vanishing_integrals μs μ hμ fs f hf
    (fun _ => infDist_nonneg) hzero hx

end PolycyclicRecognition

end

end OAI
