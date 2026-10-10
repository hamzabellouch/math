import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.MetricSpace.IsometricSMul

namespace OAI

/-! # A compatible left-invariant metric

Take the supremum of the bounded metric over left translations. The left
uniformity makes this supremum compatible with the original topology.
This supplies the metrization step in the proper chain-metric construction.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Metric Topology
open scoped Uniformity

variable {G : Type*} [Group G] [MetricSpace G]

/-- The bounded supremum over all left translations of a given metric. -/
def leftInvariantDistance (x y : G) : ℝ :=
  ⨆ g : G, min 1 (dist (g * x) (g * y))

private theorem translateDistance_bdd (x y : G) :
    BddAbove (Set.range (fun g : G => min 1 (dist (g * x) (g * y)))) :=
  ⟨1, by rintro _ ⟨g, rfl⟩; exact min_le_left _ _⟩

theorem leftInvariantDistance_le_one (x y : G) : leftInvariantDistance x y ≤ 1 :=
  ciSup_le (fun _ => min_le_left _ _)

theorem min_dist_le_leftInvariantDistance (x y : G) :
    min 1 (dist x y) ≤ leftInvariantDistance x y := by
  simpa only [one_mul, leftInvariantDistance] using le_ciSup (translateDistance_bdd x y) (1 : G)

@[simp] theorem leftInvariantDistance_self (x : G) : leftInvariantDistance x x = 0 := by
  simp [leftInvariantDistance]

theorem leftInvariantDistance_comm (x y : G) :
    leftInvariantDistance x y = leftInvariantDistance y x := by
  simp only [leftInvariantDistance, dist_comm]

private theorem min_one_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min 1 (a + b) ≤ min 1 a + min 1 b := by
  by_cases h : a ≤ 1
  · by_cases h' : b ≤ 1
    · simpa only [min_eq_right h, min_eq_right h'] using min_le_right 1 (a + b)
    · rw [min_eq_right h, min_eq_left (le_of_not_ge h')]
      exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_left (le_of_not_ge h)]
    exact (min_le_left _ _).trans (by have := le_min (by norm_num : (0 : ℝ) ≤ 1) hb; linarith)

theorem leftInvariantDistance_triangle (x y z : G) :
    leftInvariantDistance x z ≤ leftInvariantDistance x y + leftInvariantDistance y z := by
  apply ciSup_le
  intro g
  exact (min_le_min_left 1 (dist_triangle (g * x) (g * y) (g * z))).trans
    ((min_one_add_le _ _ dist_nonneg dist_nonneg).trans
      (add_le_add (le_ciSup (translateDistance_bdd x y) g)
        (le_ciSup (translateDistance_bdd y z) g)))

theorem leftInvariantDistance_mul_left (g x y : G) :
    leftInvariantDistance (g * x) (g * y) = leftInvariantDistance x y := by
  apply le_antisymm
  · apply ciSup_le
    intro h
    simpa only [mul_assoc, leftInvariantDistance] using le_ciSup (translateDistance_bdd x y) (h * g)
  · apply ciSup_le
    intro h
    simpa only [mul_assoc, inv_mul_cancel_left, leftInvariantDistance] using
      le_ciSup (translateDistance_bdd (g * x) (g * y)) (h * g⁻¹)

section LeftUniform
variable [IsLeftUniformGroup G]

/-- All left translations are equicontinuous for a metric inducing the left uniformity. -/
theorem leftTranslations_uniform_control {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : G, dist x y < δ → ∀ g : G, dist (g * x) (g * y) < ε := by
  have h : {p : G × G | dist p.1 p.2 < ε} ∈
      Filter.comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 (1 : G)) := by
    rw [← uniformity_eq_comap_inv_mul_nhds_one G]
    exact dist_mem_uniformity hε
  obtain ⟨U, hU, hsub⟩ := h
  have hpre : (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' U ∈ 𝓤 G := by
    rw [uniformity_eq_comap_inv_mul_nhds_one G]
    exact preimage_mem_comap hU
  obtain ⟨δ, hδ, hcontrol⟩ := mem_uniformity_dist.mp hpre
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy g
  exact hsub (show (g * x, g * y) ∈ (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' U by
    simpa [mul_assoc] using hcontrol hxy)

theorem leftInvariantDistance_topology (s : Set G) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, leftInvariantDistance x y < ε → y ∈ s := by
  rw [Metric.isOpen_iff]
  constructor
  · intro hs x hx
    obtain ⟨r, hr, hball⟩ := hs x hx
    refine ⟨min 1 r, lt_min zero_lt_one hr, ?_⟩
    intro y hy
    have hmin := (min_dist_le_leftInvariantDistance x y).trans_lt hy
    have hdist : dist x y < r := by
      rcases lt_min_iff.mp hmin with ⟨h1, hr'⟩
      rcases min_lt_iff.mp h1 with h | h
      · exact False.elim ((lt_irrefl (1 : ℝ)) h)
      · simpa only [min_eq_right (le_of_lt h)] using hr'
    exact hball (by simpa only [mem_ball, dist_comm] using hdist)
  · intro hs x hx
    obtain ⟨ε, hε, hball⟩ := hs x hx
    obtain ⟨δ, hδ, hcontrol⟩ := leftTranslations_uniform_control (G := G) (half_pos hε)
    refine ⟨δ, hδ, ?_⟩
    intro y hy
    apply hball y
    have hxy : dist x y < δ := by simpa only [mem_ball, dist_comm] using hy
    have hsup : leftInvariantDistance x y ≤ ε / 2 :=
      ciSup_le (fun g => (min_le_right _ _).trans (hcontrol x y hxy g).le)
    exact hsup.trans_lt (half_lt_self hε)

/-- The left-invariant metric with exactly the original topology. -/
@[instance_reducible]
def leftInvariantMetric : MetricSpace G :=
  MetricSpace.ofDistTopology leftInvariantDistance leftInvariantDistance_self
    leftInvariantDistance_comm leftInvariantDistance_triangle leftInvariantDistance_topology
    (by
      intro x y hxy
      have h := min_dist_le_leftInvariantDistance x y
      rw [hxy] at h
      have hd : dist x y ≤ 0 := (min_le_iff.mp h).resolve_left (by norm_num)
      exact dist_le_zero.mp hd)

theorem leftInvariantMetric_isometric :
    letI := leftInvariantMetric (G := G)
    IsIsometricSMul G G := by
  let m₀ : MetricSpace G := inferInstance
  let := leftInvariantMetric (G := G)
  refine ⟨fun g => Isometry.of_dist_eq ?_⟩
  intro x y
  change @leftInvariantDistance G _ m₀ (g * x) (g * y) =
    @leftInvariantDistance G _ m₀ x y
  exact @leftInvariantDistance_mul_left G _ m₀ g x y

end LeftUniform
/-- Every first-countable Hausdorff topological group has a bounded,
compatible left-invariant metric. -/
theorem exists_bounded_leftInvariant_metric
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [FirstCountableTopology H] [T2Space H] :
    ∃ m : MetricSpace H,
      m.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace H› ∧
      (letI := m; IsIsometricSMul H H) ∧
      (letI := m; ∀ x y : H, dist x y ≤ 1) := by
  let u : UniformSpace H := IsTopologicalGroup.leftUniformSpace H
  let : UniformSpace H := u
  let : IsCountablyGenerated (𝓤 H) := by
    change IsCountablyGenerated (Filter.comap (fun p : H × H => p.1⁻¹ * p.2) (𝓝 1))
    infer_instance
  let : MetricSpace H := UniformSpace.metricSpace H
  let : IsLeftUniformGroup H :=
    { uniformity_eq := rfl }
  refine ⟨leftInvariantMetric (G := H), rfl, leftInvariantMetric_isometric, ?_⟩
  intro x y
  exact leftInvariantDistance_le_one x y

end PolycyclicRecognition

end

end OAI
