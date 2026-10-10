import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.MinimizerCompactness
import OAI.Geometry.WeakMTW.Coordinates.FocalCoordinates
import OAI.Geometry.WeakMTW.Variations.GeneratingQuadratic
import OAI.Geometry.WeakMTW.Support.FirstCutSupport

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry DiscreteVariational RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem verticalCoordinates_minimizing (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ minimizingDomain x) :
    dist ((stateChart x).symm (verticalCoordinates x v)).1
      (geodesic ((stateChart x).symm (verticalCoordinates x v)) 1) =
      ‖((stateChart x).symm (verticalCoordinates x v)).2‖ := by
  have hp : (⟨x,v⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  rw [verticalCoordinates_eq,(stateChart x).left_inv hp,← exp_eq_geodesic]
  exact hv

 theorem actual_focal_trial_pole (x : M) {p e k : TangentSpace (model n) x} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hseg : ∀ s ∈ Icc (-a) b, p+s•e ∈ minimizingDomain x)
    (hk : fderiv ℝ (fun w => chartAt (Model n) (exp x p) (exp x w)) p k = 0)
    (ξ : TangentSpace (model n) x) (hξ : inner ℝ ξ k ≠ 0) :
    FirstCut.HasTrialPole (fun h s => actionHessian x ((1-h)•(p+s•e))) ξ := by
  let y := exp x p
  let κ := tangentChartLinear x k
  let W : ℝ × ℝ → TangentSpace (model n) x := fun z => (1-z.2)•(p+z.1•e)
  let q : ℝ × ℝ → Model n × Model n := fun z => verticalCoordinates x (W z)
  let A : (Model n × Model n) × Model n := ((tangentChartLinear x ξ,0),0)
  let K : (Model n × Model n) × Model n := ((0,κ),0)
  have hW : ContDiff ℝ ∞ W := (contDiff_const.sub contDiff_snd).smul (contDiff_const.add (contDiff_fst.smul contDiff_const))
  have hq : ContDiff ℝ ∞ q := (verticalCoordinates_smooth x).comp hW
  have hW₀ : W (0,0) = p := by simp [W]
  have hq₀ : q (0,0) = verticalCoordinates x p := by rw [show q (0,0) = verticalCoordinates x (W (0,0)) from rfl,hW₀]
  have hp : (⟨x,p⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  have hpt : verticalCoordinates x p ∈ (stateChart x).target := by
    rw [verticalCoordinates_eq]; exact (stateChart x).map_source hp
  have hpy : geodesicFlow 1 ((stateChart x).symm (verticalCoordinates x p)) ∈ (stateChart y).source := by
    rw [verticalCoordinates_eq,(stateChart x).left_inv hp]
    apply (stateChart_source y _).mpr
    change geodesic (⟨x,p⟩ : TangentBundle (model n) M) 1 ∈ _
    simpa only [← exp_eq_geodesic] using mem_chart_source (Model n) y
  obtain ⟨ε,hε,hε₁,hgen⟩ := exists_generating_neighborhood x y hpt hpy
  have hgen₀ := mem_of_mem_nhds hgen
  have hnear : ∀ᶠ z : ℝ × ℝ in 𝓝 (0,0), GeneratingChartAction x y ε (q z) := by
    have hc : Tendsto q (𝓝 (0,0)) (𝓝 (verticalCoordinates x p)) := hq₀ ▸ hq.continuous.continuousAt.tendsto
    exact hc hgen
  have hHs : ContDiffAt ℝ ∞ (fun z => generatingHessian x y ε (q z)) (0,0) := by
    apply ContDiffAt.comp (f := q) (g := generatingHessian x y ε) (0,0) _ hq.contDiffAt
    rw [hq₀]
    exact generatingHessian_smooth x y hgen₀
  let P : ℝ × ℝ → ℝ := fun z => generatingHessian x y ε (q z) K K
  let R : ℝ × ℝ → ℝ := fun z => generatingHessian x y ε (q z) A K
  let U : ℝ × ℝ → ℝ := fun z => generatingHessian x y ε (q z) A A +
    lowerChristoffel (fderiv ℝ (metric x) (chartAt (Model n) x x))
      (tangentChartLinear x ξ) (tangentChartLinear x ξ) (tangentChartLinear x (W z))
  have hP : ContDiffAt ℝ 2 P (0,0) :=
    ((hHs.clm_apply contDiffAt_const).clm_apply contDiffAt_const).of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hR : ContinuousAt R (0,0) := ((hHs.clm_apply contDiffAt_const).clm_apply contDiffAt_const).continuousAt
  have hU : ContinuousAt U (0,0) := by
    refine ((hHs.clm_apply contDiffAt_const).clm_apply contDiffAt_const).continuousAt.add ?_
    unfold lowerChristoffel
    have hh := (tangentChartLinear x).continuous.comp hW.continuous
    fun_prop
  have hker := fibre_kernel_state_kernel x y (mem_chart_source (Model n) y) hk
  have hPzero : P (0,0) = 0 := by
    dsimp only [P]
    rw [hq₀]
    have hh := generatingHessian_focal x y hε.ne' hgen hker 0 κ
    simpa only [K,map_zero,neg_zero] using hh
  have hRvalue : R (0,0) = -inner ℝ k ξ := by
    dsimp only [R]
    rw [hq₀,generatingHessian_symmetric x y hgen₀ A K]
    have hh := generatingHessian_focal x y hε.ne' hgen hker (tangentChartLinear x ξ) 0
    change generatingHessian x y ε (verticalCoordinates x p) K A = _ at hh
    rw [show (verticalCoordinates x p).1 = chartAt (Model n) x x from rfl] at hh
    have hmet : metric x (chartAt (Model n) x x) (tangentChartLinear x k) (tangentChartLinear x ξ) = inner ℝ k ξ :=
      metric_chart_pair x x (mem_chart_source (Model n) x) k ξ
    rw [hmet] at hh
    exact hh
  have hRzero : R (0,0) ≠ 0 := by rw [hRvalue,neg_ne_zero,real_inner_comm]; exact hξ
  have hsnear : ∀ᶠ s : ℝ in 𝓝 0, s ∈ Icc (-a) b := Icc_mem_nhds (by linarith) hb
  have hPmin : ∀ᶠ s in 𝓝 (0 : ℝ), 0 ≤ P (s,0) := by
    have hsmooth : ContinuousAt (fun s : ℝ => (s,(0 : ℝ))) 0 := continuousAt_id.prodMk continuousAt_const
    filter_upwards [hsnear,hsmooth.tendsto hnear] with s hs hgs
    have hm := hseg s hs
    have hWz : W (s,0) = p+s•e := by simp [W]
    exact generatingHessian_vertical_nonneg x y hε hε₁ hgs
      (verticalCoordinates_minimizing x (hWz.symm ▸ hm)) κ
  have hI : ∀ᶠ z : ℝ × ℝ in 𝓝 (0,0), 0 < z.2 → W z ∈ injectivityDomain x := by
    have hs := (continuousAt_fst : ContinuousAt (Prod.fst : ℝ × ℝ → ℝ) (0,0)).tendsto hsnear
    have ht : ∀ᶠ z : ℝ × ℝ in 𝓝 (0,0), z.2 < 1 :=
      continuousAt_snd.eventually_lt continuousAt_const (by norm_num)
    filter_upwards [hs,ht] with z hz ht hz₀
    exact strict_radial_mem_injectivity (hseg z.1 hz) (by linarith) (by linarith)
  have htest : ∀ᶠ z in 𝓝 ((0,0) : ℝ × ℝ), 0 < z.2 → ∀ α : ℝ,
      actionHessian x (W z) ξ ξ ≤ U z + 2*α*R z + α^2*P z := by
    filter_upwards [hnear,hI] with z hgz hIz hz α
    have hgz' : GeneratingChartAction x y ε (stateChart x (⟨x,W z⟩ : TangentBundle (model n) M)) := by
      simpa only [q,verticalCoordinates_eq] using hgz
    simpa only [U,R,P,q,verticalCoordinates_eq,A,K] using
      generating_scalar_trial x y hε hε₁ (hIz hz) hgz' ξ κ α
  have hpositive : ∀ᶠ z in 𝓝 ((0,0) : ℝ × ℝ), 0 < z.2 → 0 < P z := by
    have hRnear := hR.eventually_ne hRzero
    filter_upwards [hnear,hI,htest,hRnear] with z hgz hIz htz hRz hz
    apply GeneratingCalculus.positive_of_trial _ hRz (htz hz)
    exact generatingHessian_vertical_nonneg x y hε hε₁ hgz
      (verticalCoordinates_minimizing x (injectivity_subset_minimizing x (hIz hz))) κ
  exact FirstCut.pole_of_smooth_index_coefficients hP hPmin hPzero hU hR hRzero hpositive htest

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
