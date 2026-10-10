import Mathlib
import OAI.Analysis.SymmetricDomains.SliceGraphDerivativeBound

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

lemma sliceParameter_analytic (c : NashBoundaryChart (m := m) U V B q) (s) :
    AnalyticOnNhd ℝ (c.sliceParameter s) univ := by
  intro x _
  exact analyticAt_const.add ((normalParameterInjection _ _).analyticAt x)

lemma slice_graph_coordinates (c : NashBoundaryChart (m := m) U V B q) (s)
    (x v : Fin c.normal.normalDim → ℝ) :
    c.normal.realCoordinates (c.sliceLift s (fun j => (x j : ℂ)+Complex.I*((c.sliceGraph s x j+v j) : ℂ))) =
      (c.sliceParameter s x,c.normal.graph (c.sliceParameter s x)+v) := by
  rw [c.slice_real_coordinates]
  have hre : (fun j => ((x j : ℂ)+Complex.I*((c.sliceGraph s x j+v j) : ℂ)).re) = x := by
    funext j
    simp
  have him : (fun j => ((x j : ℂ)+Complex.I*((c.sliceGraph s x j+v j) : ℂ)).im) = c.sliceGraph s x+v := by
    funext j
    simp
  rw [hre,him]
  congr 1
  funext j
  simp only [sliceGraph,Pi.add_apply,Pi.sub_apply]
  ring

lemma slice_family_sub_and_boundary (c : NashBoundaryChart (m := m) U V B q) {s}
    (hs : s ∈ ball 0 c.graphRadius) :
    ∀ᶠ x in 𝓝 (0 : Fin c.normal.normalDim → ℝ),
      ({v | ‖v‖ < 1 ∧ (fun j => (x j : ℂ)+Complex.I*((c.sliceGraph s x j+v j) : ℂ)) ∈ c.sliceDomain s} ⊆ c.family (c.sliceParameter s x)) ∧
      (0 : Fin c.normal.normalDim → ℝ) ∉ c.family (c.sliceParameter s x) ∧
      (fun j => (x j : ℂ)+Complex.I*(c.sliceGraph s x j : ℂ)) ∉ c.sliceDomain s := by
  have ht : Tendsto (c.sliceParameter s) (𝓝 0) (𝓝 s) := by
    simpa only [sliceParameter_zero] using (c.sliceParameter_analytic s 0 (mem_univ _)).continuousAt.tendsto
  filter_upwards [ht (isOpen_ball.mem_nhds hs)] with x hx
  have hboundary := (c.graph_boundary (c.sliceParameter s x) hx).1.2
  refine ⟨?_,?_,?_⟩
  · intro v hv
    refine ⟨hx,hv.1,?_⟩
    have hvD := hv.2
    change c.normal.realCoordinates (c.sliceLift s (fun j => (x j : ℂ)+Complex.I*((c.sliceGraph s x j+v j) : ℂ))) ∈ c.chart.coordinateDomain U c.normal.realCoordinates at hvD
    rw [c.slice_graph_coordinates] at hvD
    exact hvD
  · intro hz
    apply hboundary
    simpa only [add_zero] using hz.2.2
  · intro hz
    apply hboundary
    have he : c.normal.realCoordinates (c.sliceLift s (fun j => (x j : ℂ)+Complex.I*(c.sliceGraph s x j : ℂ))) =
        (c.sliceParameter s x,c.normal.graph (c.sliceParameter s x)) := by
      simpa using c.slice_graph_coordinates s x 0
    change c.normal.realCoordinates (c.sliceLift s (fun j => (x j : ℂ)+Complex.I*(c.sliceGraph s x j : ℂ))) ∈ c.chart.coordinateDomain U c.normal.realCoordinates at hz
    rwa [he] at hz

theorem slice_approaching_graphs (c : NashBoundaryChart (m := m) U V B q) {s}
    (hs : s ∈ ball 0 c.graphRadius)
    (hdata : BoundaryOffsetData c.family (ball 0 c.graphRadius) s) :
    ∃ G : (Fin c.normal.normalDim → ℝ) × ℝ → Affine c.normal.normalDim,
      AnalyticAt ℝ G 0 ∧
      (∀ᶠ x in 𝓝 (0 : Fin c.normal.normalDim → ℝ),
        G (x,0) = fun j => (x j : ℂ)+Complex.I*(c.sliceGraph s x j : ℂ)) ∧
      ∀ᶠ p in 𝓝 (0 : (Fin c.normal.normalDim → ℝ) × ℝ), 0 < p.2 → G p ∈ c.sliceDomain s := by
  obtain ⟨r,hr,η,hη,ψ,_hrB,hψ,hψ0,hψin⟩ := hdata.1
  let J : (Fin c.normal.normalDim → ℝ) × ℝ →
      (Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) × ℝ :=
    fun p => (c.sliceParameter s p.1,p.2)
  have hfst : AnalyticAt ℝ (fun p : (Fin c.normal.normalDim → ℝ) × ℝ => p.1) 0 := analyticAt_fst
  have hJa : AnalyticAt ℝ J 0 :=
    ((c.sliceParameter_analytic s (0 : Fin c.normal.normalDim → ℝ) (mem_univ _)).comp_of_eq hfst rfl).prod analyticAt_snd
  have hJ0 : J 0 = (s,0) := by simp only [J,Prod.fst_zero,Prod.snd_zero,sliceParameter_zero]
  have hψa : AnalyticAt ℝ (ψ ∘ J) 0 := by
    have hp : AnalyticAt ℝ ψ (J 0) := by
      rw [hJ0]
      exact hψ _ ⟨mem_ball_self hr,mem_ball_self hη⟩
    exact hp.comp hJa
  let G : (Fin c.normal.normalDim → ℝ) × ℝ → Affine c.normal.normalDim :=
    fun p => Flatten.realEmbedding c.normal.normalDim p.1 +
      Complex.I • Flatten.realEmbedding c.normal.normalDim
        (c.sliceGraph s p.1+ψ (J p))
  have hreal : AnalyticAt ℝ (fun p => Flatten.realEmbedding c.normal.normalDim
      (c.sliceGraph s p.1 + ψ (J p))) 0 :=
    ((Flatten.realEmbedding _).analyticAt _).comp
      (((c.sliceGraph_analytic hs).comp_of_eq hfst rfl).add hψa)
  have hi : AnalyticAt ℝ (fun z : Affine c.normal.normalDim => Complex.I • z)
      (Flatten.realEmbedding c.normal.normalDim (c.sliceGraph s 0 + ψ (J 0))) :=
    ((Complex.I • ContinuousLinearMap.id ℂ (Affine c.normal.normalDim)).restrictScalars ℝ).analyticAt _
  have hGa : AnalyticAt ℝ G 0 :=
    ((Flatten.realEmbedding _).analyticAt _ |>.comp hfst).add (hi.comp_of_eq hreal rfl)
  have ht : Tendsto (c.sliceParameter s) (𝓝 0) (𝓝 s) := by
    simpa only [sliceParameter_zero] using (c.sliceParameter_analytic s 0 (mem_univ _)).continuousAt.tendsto
  refine ⟨G,hGa,?_,?_⟩
  · filter_upwards [ht (ball_mem_nhds s hr)] with x hx
    have hz := hψ0 _ hx
    change G (x,0) = _
    simp only [G,J,hz,add_zero]
    rfl
  · have hJt : Tendsto J (𝓝 0) (𝓝 (s,0)) := hJ0 ▸ hJa.continuousAt.tendsto
    have hn : ball s r ×ˢ ball 0 η ∈ 𝓝 (s,(0:ℝ)) :=
      (isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hr,mem_ball_self hη⟩
    filter_upwards [hJt hn] with p hp
    intro hp0
    have hplt : p.2 < η := by
      have h := mem_ball_zero_iff.mp hp.2
      exact (le_abs_self p.2).trans_lt h
    have hin := hψin _ hp.1 p.2 ⟨hp0,hplt⟩
    change c.normal.realCoordinates (c.sliceLift s (G p)) ∈ c.chart.coordinateDomain U c.normal.realCoordinates
    have he : G p = fun j => (p.1 j : ℂ)+Complex.I*((c.sliceGraph s p.1 j+(ψ (J p)) j) : ℂ) := by
      funext coordinate
      change (p.1 coordinate : ℂ) + Complex.I *
          ((c.sliceGraph s p.1 coordinate + ψ (J p) coordinate : ℝ) : ℂ) = _
      rw [Complex.ofReal_add]
    rw [he,c.slice_graph_coordinates]
    exact hin.2.2
end Release061.NashBoundaryChart

end

end OAI
