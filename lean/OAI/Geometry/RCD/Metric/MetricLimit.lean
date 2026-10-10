import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# Metric estimates for limiting regular-point coordinates

These lemmas isolate the elementary metric part of the passage to a limiting
chart.  An approximating map may be selected separately for each pair of
points; no global injectivity of an approximating map is required.
-/

open Filter
open scoped Topology

namespace RegularPointCoordinates

/-- The dyadic scale used for a pair of points in the limiting-chart argument. -/
theorem exists_dyadic_scale {t : ℝ} (ht : 0 < t) (htone : t ≤ 1) :
    ∃ i : ℕ, t ≤ (1 / 2 : ℝ) ^ i ∧ (1 / 2 : ℝ) ^ i < 2 * t := by
  obtain ⟨i, hi, hti⟩ :=
    exists_nat_pow_near_of_lt_one ht htone (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨i, hti, ?_⟩
  rw [pow_succ] at hi
  nlinarith

section PseudoMetric

variable {X Y ι : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- Two-sided distance estimates are preserved under pointwise convergence. -/
theorem dist_bounds_of_pointwise_limit {l : Filter ι} [l.NeBot]
    {f : ι → X → Y} {F : X → Y} {a b : ℝ}
    (hlim : ∀ x, Tendsto (fun i => f i x) l (𝓝 (F x)))
    (hbound : ∀ᶠ i in l, ∀ x z,
      a * dist x z ≤ dist (f i x) (f i z) ∧
      dist (f i x) (f i z) ≤ b * dist x z) (x z : X) :
    a * dist x z ≤ dist (F x) (F z) ∧
      dist (F x) (F z) ≤ b * dist x z := by
  have hdist := (hlim x).dist (hlim z)
  exact ⟨ge_of_tendsto hdist (hbound.mono fun i hi => (hi x z).1),
    le_of_tendsto hdist (hbound.mono fun i hi => (hi x z).2)⟩

/-- A pairwise bound loses only the sum of the two endpoint errors. -/
theorem dist_bounds_of_approximation {F f : X → Y} {a b e : ℝ} (x z : X)
    (hlower : a * dist x z ≤ dist (f x) (f z))
    (hupper : dist (f x) (f z) ≤ b * dist x z)
    (herror : dist (F x) (f x) + dist (F z) (f z) ≤ e * dist x z) :
    (a - e) * dist x z ≤ dist (F x) (F z) ∧
      dist (F x) (F z) ≤ (b + e) * dist x z := by
  have hforward := dist_triangle4 (F x) (f x) (f z) (F z)
  have hbackward := dist_triangle4 (f x) (F x) (F z) (f z)
  rw [dist_comm (f z) (F z)] at hforward
  rw [dist_comm (f x) (F x)] at hbackward
  constructor <;> nlinarith

/-- The scale of an approximating map is allowed to depend on both points. -/
theorem dist_bounds_of_pairwise_approximants
    {f : ι → X → Y} {F : X → Y} {a b e : ℝ}
    (happrox : ∀ x z, ∃ i,
      a * dist x z ≤ dist (f i x) (f i z) ∧
      dist (f i x) (f i z) ≤ b * dist x z ∧
      dist (F x) (f i x) + dist (F z) (f i z) ≤ e * dist x z)
    (x z : X) :
    (a - e) * dist x z ≤ dist (F x) (F z) ∧
      dist (F x) (F z) ≤ (b + e) * dist x z := by
  obtain ⟨i, hlower, hupper, herror⟩ := happrox x z
  exact dist_bounds_of_approximation x z hlower hupper herror

/-- The upper metric estimate supplies the continuity needed for a chart. -/
theorem continuous_of_dist_upper_bound {F : X → Y} {b : ℝ}
    (hupper : ∀ x z, dist (F x) (F z) ≤ b * dist x z) : Continuous F :=
  (LipschitzWith.of_dist_le' hupper).continuous

omit [PseudoMetricSpace X] in
/-- Geometric step bounds construct the limiting map and a uniform quantitative
tail bound.  This is applied to the renormalized maps on their common domain. -/
theorem exists_limit_of_geometric_step [CompleteSpace Y]
    {f : ℕ → X → Y} {r C : ℝ} (hr : r < 1)
    (hstep : ∀ i x, dist (f i x) (f (i + 1) x) ≤ C * r ^ i) :
    ∃ F : X → Y,
      (∀ x, Tendsto (fun i => f i x) atTop (𝓝 (F x))) ∧
      ∀ i x, dist (f i x) (F x) ≤ C * r ^ i / (1 - r) := by
  have hpoint : ∀ x, ∃ y, Tendsto (fun i => f i x) atTop (𝓝 y) := fun x =>
    cauchySeq_tendsto_of_complete
      (cauchySeq_of_le_geometric r C hr fun i => hstep i x)
  refine ⟨fun x => Classical.choose (hpoint x), ?_, ?_⟩
  · intro x
    exact Classical.choose_spec (hpoint x)
  · intro i x
    exact dist_le_of_le_geometric_of_tendsto r C hr (fun j => hstep j x)
      (Classical.choose_spec (hpoint x)) i

end PseudoMetric

section Metric

variable {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]

/-- A positive lower distance bound separates every pair of source points. -/
theorem injective_of_dist_lower_bound {F : X → Y} {a : ℝ} (ha : 0 < a)
    (hlower : ∀ x z, a * dist x z ≤ dist (F x) (F z)) : Function.Injective F := by
  intro x z hxz
  have h := hlower x z
  rw [hxz, dist_self] at h
  have hdist : dist x z = 0 := by
    nlinarith [dist_nonneg (x := x) (y := z)]
  exact dist_eq_zero.mp hdist

/-- A two-sided distance estimate gives the standard Lipschitz and
antilipschitz predicates with reciprocal constants. -/
theorem lipschitz_antilipschitz_of_dist_bounds {F : X → Y} {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b)
    (hbound : ∀ x z,
      a * dist x z ≤ dist (F x) (F z) ∧
      dist (F x) (F z) ≤ b * dist x z) :
    LipschitzWith ⟨b, hb⟩ F ∧ AntilipschitzWith ⟨a⁻¹, inv_nonneg.mpr ha.le⟩ F := by
  constructor
  · exact LipschitzWith.of_dist_le_mul fun x z => (hbound x z).2
  · apply AntilipschitzWith.of_le_mul_dist
    intro x z
    change dist x z ≤ a⁻¹ * dist (F x) (F z)
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ ha).mpr
    simpa only [mul_comm] using (hbound x z).1

end Metric

end RegularPointCoordinates

end OAI
