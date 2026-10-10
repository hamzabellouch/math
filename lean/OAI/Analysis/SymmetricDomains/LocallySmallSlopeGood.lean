import Mathlib
import OAI.Analysis.SymmetricDomains.LocallyGoodNashBoundary
import OAI.Analysis.SymmetricDomains.InteriorBallsSmallSlope

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

section
open Set Filter Topology Metric

theorem offset_joint_excluded_subfamily {S X E : Type*} [TopologicalSpace S]
    [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : S → Set E) (B : X → Set E) {i : X → S} {x₀ : X} {s₀ : S}
    (hi : Tendsto i (𝓝 x₀) (𝓝 s₀))
    (hBA : ∀ᶠ x in 𝓝 x₀, B x ⊆ A (i x))
    (h0 : ∀ᶠ x in 𝓝 x₀, (0 : E) ∉ A (i x))
    (f : E → ℝ)
    (hf : ∀ y, Tendsto (fun p : S × ℝ => offsetDistance A p.1 p.2 y)
      (𝓝[{p : S × ℝ | 0 < p.2}] (s₀,0)) (𝓝 (f y)))
    (s : ℕ → X) (t : ℕ → ℝ) (v : ℕ → E) (w : E)
    (hs : Tendsto s atTop (𝓝 x₀)) (ht : Tendsto t atTop (𝓝 0))
    (hpos : ∀ j, 0 < t j) (hv : Tendsto v atTop (𝓝 w)) (hw : f w = 0) :
    Tendsto (fun j => infDist (v j) (offsetScaled B (s j) (t j))ᶜ) atTop (𝓝 0) := by
  have hlim := offset_joint_excluded_limit A hf (hi.comp hs) ht
    (Eventually.of_forall hpos) hv hw
  apply squeeze_zero' (Eventually.of_forall fun _ => infDist_nonneg)
    ?_ hlim
  filter_upwards [hs hBA,hs h0] with j hBj h0j
  apply infDist_le_infDist_of_subset ?_ (offset_excluded_nonempty A (i (s j)) (t j) h0j)
  exact compl_subset_compl.mpr (fun y hy => hBj hy)

theorem small_slope_family_noncollapse {S : Type*} [TopologicalSpace S]
    {k : ℕ} {Ω : Set (Fin k → ℂ)} (hΩ : IsOpen Ω)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hCP : Wiener.DiscContinuityWithin k Ω ε)
    {φ : (Fin k → ℝ) → Fin k → ℝ} (hφ : AnalyticAt ℝ φ 0) (hφ0 : φ 0 = 0)
    (hdφ : ‖fderiv ℝ φ 0‖ < 1/2)
    {G : (Fin k → ℝ) × ℝ → Fin k → ℂ} (hG : AnalyticAt ℝ G 0)
    (hG0 : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ),
      G (x,0) = fun j => (x j : ℂ)+Complex.I*(φ x j : ℂ))
    (hGΩ : ∀ᶠ p in 𝓝 (0 : (Fin k → ℝ) × ℝ), 0 < p.2 → G p ∈ Ω)
    (hbdry : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ),
      (fun j => (x j : ℂ)+Complex.I*(φ x j : ℂ)) ∉ Ω)
    (A : S → Set (Fin k → ℝ)) {i : (Fin k → ℝ) → S} {s₀ : S}
    (hi : Tendsto i (𝓝 0) (𝓝 s₀))
    (hBA : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ),
      {v | ‖v‖ < ρ ∧ (fun j => (x j : ℂ)+Complex.I*((φ x j+v j) : ℂ)) ∈ Ω} ⊆ A (i x))
    (h0 : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), (0 : Fin k → ℝ) ∉ A (i x))
    (f : (Fin k → ℝ) → ℝ)
    (hf : ∀ y, Tendsto (fun p : S × ℝ => offsetDistance A p.1 p.2 y)
      (𝓝[{p : S × ℝ | 0 < p.2}] (s₀,0)) (𝓝 (f y))) : {y | f y = 0} ≠ univ := by
  obtain ⟨c,C,t₀,hc,hC,ht₀,hballs⟩ := interior_balls_from_small_slope_graphs
    hΩ hε hCP hφ hφ0 hdφ hG hG0 hGΩ
  apply normal_offset_noncollapse hφ.contDiffAt hφ0 hρ hc hC ht₀ hballs hbdry {y | f y = 0}
  intro s t v w hs ht hpos hv hw
  exact offset_joint_excluded_subfamily A _ hi hBA h0 f hf s t v w hs ht hpos hv hw
end

open Set Filter Topology Metric MeasureTheory
open scoped Classical

def SmallSlopeGoodNashBoundary {d N : ℕ} (m : ℕ) (U V : Set (Affine N))
    (B : Set (Fin d → ℝ)) (q : (Fin d → ℝ) → Affine N) (x : Fin d → ℝ) : Prop :=
  ∃ c : NashBoundaryChart (m := m) U V B q, c.GoodAt x ∧
    ‖fderiv ℝ c.normal.graph (c.normal.parameters x)‖ < 1/2

theorem NashBoundaryChart.locally_small_slope_good {d m N : ℕ} {U V : Set (Affine N)}
    {B : Set (Fin d → ℝ)} {q : (Fin d → ℝ) → Affine N}
    (c : NashBoundaryChart (m := m) U V B q) :
    ∃ W : Set (Fin d → ℝ), IsOpen W ∧ c.center ∈ W ∧
      volume {x | x ∈ W ∧ ¬ SmallSlopeGoodNashBoundary m U V B q x} = 0 := by
  obtain ⟨W,hWo,haW,hnull⟩ := c.null_bad_parameters
  have hcd : ContinuousAt (fderiv ℝ c.normal.graph) 0 :=
    ((c.normal.graph_analytic 0 (mem_ball_self c.normal.radius_pos)).contDiffAt (n := 1)).continuousAt_fderiv (by norm_num)
  have hnear : ∀ᶠ s in 𝓝 0, ‖fderiv ℝ c.normal.graph s‖ < 1/2 :=
    hcd.norm (gt_mem_nhds (by simpa only [c.normal.derivative_zero,norm_zero] using (show (0:ℝ) < 1/2 by norm_num)))
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hnear
  let T := c.normal.parameters.source ∩ c.normal.parameters ⁻¹' ball 0 r
  have hTo : IsOpen T := c.normal.parameters.isOpen_inter_preimage isOpen_ball
  have haT : c.center ∈ T := by
    refine ⟨c.normal.source_mem,?_⟩
    change c.normal.parameters c.center ∈ ball 0 r
    rw [c.normal.parameter_eq]
    simpa only [sub_self,map_zero,Prod.fst_zero] using (mem_ball_self (x :=
      (0 : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ)) hr)
  refine ⟨W ∩ T,hWo.inter hTo,⟨haW,haT⟩,measure_mono_null ?_ hnull⟩
  intro x hx
  exact ⟨hx.1.1,fun hg => hx.2 ⟨c,hg,hrs hx.1.2.2⟩⟩

theorem locally_small_slope_good_nash_boundary {d m N : ℕ}
    (U V : Set (Affine N)) (hUV : U ⊆ V) (hV : IsClosed V) (hUs : IsSemialgebraic U)
    (B : Set (Fin d → ℝ)) (hB : IsOpen B)
    (q : (Fin d → ℝ) → Affine N) (hqa : AnalyticOnNhd ℝ q B)
    (hqs : SemialgebraicOn B (fun x => complexRealEquiv N (q x)))
    (hqb : ∀ x ∈ B, q x ∈ closure U \ U)
    {a : Fin d → ℝ} (ha : a ∈ B)
    (hqi : Function.Injective (fderiv ℝ q a))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) a (Pi.single i 1)))
    (c : ProjectionNashChart V (q a) m) :
    ∃ W : Set (Fin d → ℝ), IsOpen W ∧ a ∈ W ∧
      volume {x | x ∈ W ∧ ¬ SmallSlopeGoodNashBoundary m U V B q x} = 0 := by
  obtain ⟨c,hca⟩ := nash_boundary_chart_of_projection U V hUV hV hUs B hB q hqa hqs hqb ha hqi hr c
  obtain ⟨W,hW,hcW,hnull⟩ := c.locally_small_slope_good
  refine ⟨W,hW,hca ▸ hcW,measure_mono_null ?_ hnull⟩
  intro x hx
  exact ⟨hx.1,hx.2⟩
end Release061

end

end OAI
