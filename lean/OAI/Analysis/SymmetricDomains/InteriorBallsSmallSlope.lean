import Mathlib
import OAI.Analysis.SymmetricDomains.InteriorBallsAnalyticGraphs
import OAI.Analysis.SymmetricDomains.AnalyticFamilyRegraph
import OAI.Analysis.SymmetricDomains.InteriorBallsChangeCoordinates
import OAI.Analysis.SymmetricDomains.SmallSlopeGraphComplexification

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
namespace Release061
open Set Filter Metric
open scoped Topology

theorem interior_balls_from_small_slope_graphs {k : ℕ} {Ω : Set (Fin k → ℂ)}
    (hΩ : IsOpen Ω) {ε : ℝ} (hε : 0 < ε) (hCP : Wiener.DiscContinuityWithin k Ω ε)
    {φ : (Fin k → ℝ) → Fin k → ℝ} (hφ : AnalyticAt ℝ φ 0) (hφ0 : φ 0 = 0)
    (hdφ : ‖fderiv ℝ φ 0‖ < 1/2)
    {G : (Fin k → ℝ) × ℝ → Fin k → ℂ} (hG : AnalyticAt ℝ G 0)
    (hG0 : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ),
      G (x,0) = fun i => (x i : ℂ)+Complex.I*(φ x i : ℂ))
    (hGΩ : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), 0 < q.2 → G q ∈ Ω) :
    ∃ c C t₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ →
      ∃ a : Fin k → ℂ, ‖a‖ ≤ C*t ∧ ball a (c*t) ⊆ Ω := by
  obtain ⟨e,hem,he0,he,hei,hbase⟩ := Flatten.small_slope_graph_complexification hφ hφ0 hdφ
  have htar : (0 : Fin k → ℂ) ∈ e.target := he0 ▸ e.map_source hem
  have hei0 : e.symm 0 = 0 := by
    calc e.symm 0 = e.symm (e 0) := congrArg e.symm he0.symm
         _ = 0 := e.left_inv hem
  have hGzero : G 0 = 0 := by
    have hh := hG0.self_of_nhds
    change G (0,0) = fun _ => 0
    simpa only [hφ0,Pi.zero_apply,Complex.ofReal_zero,mul_zero,add_zero] using hh
  let Ω' := e.source ∩ e ⁻¹' Ω
  let G' : (Fin k → ℝ) × ℝ → Fin k → ℂ := e.symm ∘ G
  have hG' : AnalyticAt ℝ G' 0 := by
    have hi : AnalyticAt ℝ e.symm (G 0) := by rw [hGzero]; exact hei.restrictScalars
    exact hi.comp hG
  have hG'base : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), G' (x,0) = Flatten.realEmbedding k x := by
    have ht : Tendsto (Flatten.realEmbedding k) (𝓝 0) (𝓝 (0 : Fin k → ℂ)) := by
      simpa only [map_zero] using (Flatten.realEmbedding k).continuous.continuousAt.tendsto (x := 0)
    filter_upwards [hG0,hbase,ht (e.open_source.mem_nhds hem)] with x hx hx' hxs
    change e.symm (G (x,0)) = Flatten.realEmbedding k x
    rw [hx,← hx',e.left_inv hxs]
  have hG'Ω : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), 0 < q.2 → G' q ∈ Ω' := by
    have ht : Tendsto G (𝓝 0) (𝓝 (0 : Fin k → ℂ)) := by
      simpa only [hGzero] using hG.continuousAt.tendsto
    filter_upwards [hGΩ,ht (e.open_target.mem_nhds htar)] with q hq hqt
    intro hu
    exact ⟨e.map_target hqt,by change e (e.symm (G q)) ∈ Ω; rw [e.right_inv hqt]; exact hq hu⟩
  obtain ⟨f,hf,hf0,hfΩ⟩ := Flatten.analytic_family_regraph hG' hG'base hG'Ω
  have het : Tendsto e (𝓝 0) (𝓝 (0 : Fin k → ℂ)) := by
    simpa only [he0] using he.continuousAt.tendsto
  have hnh : ∀ᶠ z in 𝓝 (0 : Fin k → ℂ),
      AnalyticAt ℂ e z ∧ z ∈ e.source ∧ e z ∈ ball 0 ε :=
    he.eventually_analyticAt.and (Filter.Eventually.and (e.open_source.mem_nhds hem) (het (ball_mem_nhds _ hε)))
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hnh
  have hCP' : Wiener.DiscContinuityWithin k Ω' r :=
    Wiener.discContinuityWithin_pullback hCP (fun z hz => (hrs hz).1)
      (fun z hz => (hrs hz).2.1) (fun z hz => (hrs hz).2.2)
  obtain ⟨c,C,t₀,hc,hC,ht₀,hballs⟩ := Wiener.interior_balls_from_analytic_graphs
    (e.isOpen_inter_preimage hΩ) hr hCP' hf hf0 hfΩ
  have her : ContDiffAt ℝ 1 e 0 := he.restrictScalars.contDiffAt
  have heir : ContDiffAt ℝ 1 e.symm 0 := hei.restrictScalars.contDiffAt
  obtain ⟨d,D,t₁,hd,hD,ht₁,hballs'⟩ :=
    interior_balls_change_coordinates e hem he0 her heir hc hC ht₀ hballs
  refine ⟨d,D,t₁,hd,hD,ht₁,?_⟩
  intro t ht htt
  obtain ⟨a,ha,hab⟩ := hballs' t ht htt
  refine ⟨a,ha,?_⟩
  intro z hz
  obtain ⟨y,hy,rfl⟩ := hab hz
  exact hy.1.2

end Release061

end

end OAI
