import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.FderivMetricPairing

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] in
theorem sphere_immersion_spans (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ v w : E, g.inner x v w =
      inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w))
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1)
    (hd : Module.finrank ℝ V = Module.finrank ℝ E + 1) :
    ∀ b : V, ∃ z : E, ∃ t : ℝ, b = fderiv ℝ F x z + t • F x := by
  let A := (fderiv ℝ F x).toLinearMap
  have hinj : Function.Injective A := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro v hv
    have hz : fderiv ℝ F x v = 0 := hv
    by_contra hnz
    have hp := g.pos x v hnz
    rw [hg, hz, inner_zero_left] at hp
    exact (lt_irrefl 0 hp)
  have hp : F x ≠ 0 := by
    intro hz
    have hh := hn.self_of_nhds
    simp [hz] at hh
  let P : Submodule ℝ V := (ℝ ∙ F x)ᗮ
  have hle : LinearMap.range A ≤ P := by
    rintro _ ⟨v,rfl⟩
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    rw [real_inner_comm]
    exact sphere_immersion_normal_first hF hn v
  have : Fact (Module.finrank ℝ V = Module.finrank ℝ E + 1) := ⟨hd⟩
  have hr : Module.finrank ℝ (LinearMap.range A) = Module.finrank ℝ P := by
    rw [LinearMap.finrank_range_of_inj hinj]
    exact (Submodule.finrank_orthogonal_span_singleton hp).symm
  have he : LinearMap.range A = P := Submodule.eq_of_le_of_finrank_eq hle hr
  intro b
  have hb : b - (inner ℝ (F x) b) • F x ∈ P := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp only [inner_sub_left, real_inner_smul_left, hn.self_of_nhds]
    rw [real_inner_comm b (F x)]
    ring
  rw [← he] at hb
  obtain ⟨z,hz⟩ := hb
  refine ⟨z,inner ℝ (F x) b,?_⟩
  change b = A z + _
  rw [hz]
  module

end YauCounterexamples

end

end OAI
