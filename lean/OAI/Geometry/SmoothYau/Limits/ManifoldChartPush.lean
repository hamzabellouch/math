import Mathlib

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
open Set Filter Manifold
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

def manifoldChartPush (p : M) (f : E → V) : M → V :=
  (chartAt E p).source.indicator (f ∘ chartAt E p)

omit [NormedSpace ℝ E] [NormedSpace ℝ V] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
lemma manifoldChartPush_apply (p : M) (f : E → V) {y : E}
    (hy : y ∈ (chartAt E p).target) :
    manifoldChartPush p f ((chartAt E p).symm y) = f y := by
  simp only [manifoldChartPush, Set.indicator_of_mem ((chartAt E p).map_target hy),
    Function.comp_apply, (chartAt E p).right_inv hy]

omit [NormedSpace ℝ E] [NormedSpace ℝ V] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
lemma manifoldChartPush_support (p : M) (f : E → V) :
    Function.support (manifoldChartPush p f) ⊆ (chartAt E p).symm '' tsupport f := by
  intro x hx
  have hs : x ∈ (chartAt E p).source := by
    by_contra hh
    exact hx (by simp [manifoldChartPush, hh])
  refine ⟨chartAt E p x, subset_closure ?_, (chartAt E p).left_inv hs⟩
  simpa only [manifoldChartPush, Set.indicator_of_mem hs, Function.comp_apply,
    Function.mem_support] using hx

omit [NormedSpace ℝ E] [NormedSpace ℝ V] [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma manifoldChartPush_tsupport (p : M) {f : E → V}
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ (chartAt E p).target) :
    tsupport (manifoldChartPush p f) ⊆ (chartAt E p).symm '' tsupport f := by
  apply closure_minimal (manifoldChartPush_support p f)
  exact (hc.image_of_continuousOn ((chartAt E p).continuousOn_symm.mono hs)).isClosed

omit [NormedSpace ℝ E] [NormedSpace ℝ V] [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma manifoldChartPush_compact (p : M) {f : E → V}
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ (chartAt E p).target) :
    HasCompactSupport (manifoldChartPush p f) :=
  (hc.image_of_continuousOn ((chartAt E p).continuousOn_symm.mono hs)).of_isClosed_subset
    isClosed_closure (manifoldChartPush_tsupport p hc hs)

lemma contMDiff_manifoldChartPush (p : M) {f : E → V}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (chartAt E p).target) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ (manifoldChartPush p f) := by
  intro x
  by_cases hx : x ∈ (chartAt E p).source
  · have he : manifoldChartPush p f =ᶠ[𝓝 x] f ∘ chartAt E p := by
      filter_upwards [(chartAt E p).open_source.mem_nhds hx] with z hz
      exact Set.indicator_of_mem hz _
    apply ((contMDiff_iff_contDiff.mpr hf).contMDiffAt.comp x
      (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hx)).congr_of_eventuallyEq he
  · have hn : x ∉ (chartAt E p).symm '' tsupport f := by
      rintro ⟨y, hy, rfl⟩
      exact hx ((chartAt E p).map_target (hs hy))
    have ht : x ∉ tsupport (manifoldChartPush p f) :=
      fun h => hn (manifoldChartPush_tsupport p hc hs h)
    exact contMDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp ht)

end YauCounterexamples

end

end OAI
