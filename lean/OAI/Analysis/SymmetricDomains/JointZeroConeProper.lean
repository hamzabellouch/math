import Mathlib
import OAI.Analysis.SymmetricDomains.CocompactChartDiscContinuity
import OAI.Analysis.SymmetricDomains.LocallySmallSlopeGood
import OAI.Analysis.SymmetricDomains.SliceApproachingGraphs

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.NashBoundaryChart
open Set Filter Topology Metric
open scoped Classical
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

lemma sliceDomain_iff (c : NashBoundaryChart (m := m) U V B q) (s) (w) :
    w ∈ c.sliceDomain s ↔ ‖complexRealEquiv m (c.sliceLift s w)‖ < c.chart.radius ∧
      c.chart.inverse (c.sliceLift s w) ∈ U := by
  change (‖complexRealEquiv m (c.normal.realCoordinates.symm (c.normal.realCoordinates (c.sliceLift s w)))‖ < c.chart.radius ∧
      c.chart.inverse (c.normal.realCoordinates.symm (c.normal.realCoordinates (c.sliceLift s w))) ∈ U) ↔ _
  rw [c.normal.realCoordinates.symm_apply_apply]

theorem slice_disc_continuity {Γ : Type*}
    (c : NashBoundaryChart (m := m) U V B q) {s}
    (hs : s ∈ ball 0 c.graphRadius) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
    [LocallyCompactSpace U] (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x) :
    ∃ ε : ℝ, 0 < ε ∧ Wiener.DiscContinuityWithin c.normal.normalDim (c.sliceDomain s) ε := by
  have hz : ‖complexRealEquiv m (c.sliceLift s 0)‖ < c.chart.radius := by
    simpa only [sliceLift,map_zero,add_zero] using (c.graph_boundary s hs).2.1
  have hn : ∀ᶠ w in 𝓝 (0 : Affine c.normal.normalDim),
      ‖complexRealEquiv m (c.sliceLift s w)‖ < c.chart.radius :=
    ((complexRealEquiv m).continuous.continuousAt.comp
      (c.sliceLift_analytic s 0 (mem_univ _)).continuousAt).norm.eventually_lt continuousAt_const hz
  obtain ⟨ε,hε,hsmall⟩ := Metric.mem_nhds_iff.mp hn
  let Φ : Affine c.normal.normalDim → Affine N := c.chart.inverse ∘ c.sliceLift s
  have hΦ : AnalyticOnNhd ℂ Φ (ball 0 ε) := by
    intro w hw
    exact (c.chart.inverse_analytic _ (hsmall hw)).comp (c.sliceLift_analytic s w (mem_univ _))
  have hΦV : MapsTo Φ (ball 0 ε) V := fun w hw => c.chart.inverse_mem _ (hsmall hw)
  have hCP := bounded_cocompact_chart_disc_continuity V U hUV hU hbounded hhol K hK hrep Φ hΦ hΦV
  refine ⟨ε,hε,?_⟩
  intro A hA hAh hAr hbd hstart
  have hall := hCP A hA hAh hAr
    (fun t z hz => ((c.sliceDomain_iff s _).mp (hbd t z hz)).2)
    (fun z => ((c.sliceDomain_iff s _).mp (hstart z)).2)
  intro t z
  apply (c.sliceDomain_iff s _).mpr
  exact ⟨hsmall (mem_ball_zero_iff.mpr (hAr t z)),hall t z⟩

theorem joint_zero_cone_proper {Γ : Type*}
    (c : NashBoundaryChart (m := m) U V B q) {s}
    (hs : s ∈ ball 0 c.graphRadius)
    (hd : ‖fderiv ℝ c.normal.graph s‖ < 1/2)
    (hdata : BoundaryOffsetData c.family (ball 0 c.graphRadius) s)
    (hUV : U ⊆ V) (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
    [LocallyCompactSpace U] (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x)
    (f : (Fin c.normal.normalDim → ℝ) → ℝ)
    (hf : ∀ y, Tendsto (fun p : (Fin (c.normal.tangentDim+c.normal.tangentDim+c.normal.normalDim) → ℝ) × ℝ =>
        offsetDistance c.family p.1 p.2 y)
      (𝓝[{p | 0 < p.2}] (s,0)) (𝓝 (f y))) : {y | f y = 0} ≠ univ := by
  obtain ⟨ε,hε,hCP⟩ := c.slice_disc_continuity hs hUV hU hbounded hhol K hK hrep
  obtain ⟨G,hG,hG0,hGU⟩ := c.slice_approaching_graphs hs hdata
  have hlocal := c.slice_family_sub_and_boundary hs
  have hi : Tendsto (c.sliceParameter s) (𝓝 0) (𝓝 s) := by
    simpa only [sliceParameter_zero] using (c.sliceParameter_analytic s 0 (mem_univ _)).continuousAt.tendsto
  exact small_slope_family_noncollapse (c.sliceDomain_isOpen hU s) hε zero_lt_one hCP
    (c.sliceGraph_analytic hs) (c.sliceGraph_zero s) ((c.sliceGraph_derivative_bound hs).trans_lt hd)
    hG hG0 hGU (hlocal.mono fun _ h => h.2.2) c.family hi
    (hlocal.mono fun _ h => h.1) (hlocal.mono fun _ h => h.2.1) f hf
end Release061.NashBoundaryChart

end

end OAI
