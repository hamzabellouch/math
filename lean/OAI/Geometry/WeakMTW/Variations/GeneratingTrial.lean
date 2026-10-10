import Mathlib
import OAI.Geometry.WeakMTW.Variations.ActionHessian
import OAI.Geometry.WeakMTW.Variations.MajorantHessian
import OAI.Geometry.WeakMTW.Variations.GeneratingHessian

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

 theorem generatingHessian_cost_trial (x y : M) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    {q : Model n × Model n} (hq : GeneratingChartAction x y ε q)
    (hm : dist ((stateChart x).symm q).1 (geodesic ((stateChart x).symm q) 1) = ‖((stateChart x).symm q).2‖)
    (hg : ContDiffAt ℝ 2 (initialCost x ((chartAt (Model n) y).symm (crossFlowCoordinates x y 1 q).1)) q.1)
    (k : Model n × Model n) :
    fderiv ℝ (fderiv ℝ (initialCost x ((chartAt (Model n) y).symm (crossFlowCoordinates x y 1 q).1))) q.1 k.1 k.1 ≤
      generatingHessian x y ε q (k,0) (k,0) := by
  let z := (crossFlowCoordinates x y 1 q).1
  let f : Model n × Model n → ℝ := fun r => generatingAction x y ε (r,z)
  let g := initialCost (n := n) x ((chartAt (Model n) y).symm z)
  have hF := hq.smooth.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hf : ContDiffAt ℝ 2 f q := hF.comp q (contDiffAt_id.prodMk contDiffAt_const)
  have hqnear : ∀ᶠ r in 𝓝 q, r ∈ (stateChart x).target ∧
      geodesicFlow (1-ε) ((stateChart x).symm r) ∈ (stateChart y).source := by
    refine inter_mem ((stateChart x).open_target.mem_nhds hq.1) ?_
    exact ((geodesicFlow_smooth_fixed (1-ε)).continuous.continuousAt.comp
      ((stateChart x).symm.continuousAt hq.1)).preimage_mem_nhds
        ((stateChart y).open_source.mem_nhds hq.2.1)
  have heq : f q = g q.1 := generatingAction_eq_minimizing x y hε hε₁ hq.1 hq.2.1 hq.2.2.1 hm
  have hle : ∀ᶠ r in 𝓝 q, g r.1 ≤ f r := by
    filter_upwards [hqnear] with r hr
    exact generatingAction_bound x y hε hε₁ hr.1 hr.2 z
  have hb := hessian_majorant (ContinuousLinearMap.fst ℝ (Model n) (Model n)) hf hg heq hle k
  let L : (Model n × Model n) →L[ℝ] ((Model n × Model n) × Model n) :=
    (ContinuousLinearMap.id ℝ (Model n × Model n)).prod 0
  let c : (Model n × Model n) × Model n := (0,z)
  have he : c+L q = (q,z) := by simp [c,L]
  have hF' : ContDiffAt ℝ 2 (generatingAction x y ε) (c+L q) := he.symm ▸ hF
  have hchain := hessian_affine_pullback L c hF' k
  have hchain' : fderiv ℝ (fderiv ℝ f) q k k = generatingHessian x y ε q (k,0) (k,0) := by
    simpa [f,z,generatingHessian,L,c] using hchain
  exact hchain' ▸ hb

 theorem generating_action_trial (x y : M) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    {v : TangentSpace (model n) x} (hv : v ∈ injectivityDomain x)
    (hq : GeneratingChartAction x y ε (stateChart x (⟨x,v⟩ : TangentBundle (model n) M)))
    (ξ : TangentSpace (model n) x) (κ : Model n) (α : ℝ) :
    actionHessian x v ξ ξ ≤
      generatingHessian x y ε (stateChart x (⟨x,v⟩ : TangentBundle (model n) M))
        ((tangentChartLinear x ξ,α•κ),0) ((tangentChartLinear x ξ,α•κ),0) +
      lowerChristoffel (fderiv ℝ (metric x) (chartAt (Model n) x x))
        (tangentChartLinear x ξ) (tangentChartLinear x ξ) (tangentChartLinear x v) := by
  let p : TangentBundle (model n) M := ⟨x,v⟩
  let q := stateChart (E := Model n) x p
  have hp : p ∈ (stateChart x).source := (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  have hi : (stateChart x).symm q = p := (stateChart x).left_inv hp
  have hY : (chartAt (Model n) y).symm (crossFlowCoordinates x y 1 q).1 = exp x v := by
    dsimp only [crossFlowCoordinates]
    rw [hi]
    have hys : geodesic p 1 ∈ (chartAt (Model n) y).source := by
      have hh : geodesic ((stateChart x).symm q) 1 ∈ (chartAt (Model n) y).source :=
        (stateChart_source y _).mp hq.2.2.1
      rw [hi] at hh
      exact hh
    change (chartAt (Model n) y).symm ((chartAt (Model n) y) (geodesic p 1)) = _
    rw [(chartAt (Model n) y).left_inv hys,← exp_eq_geodesic]
  have hm : dist ((stateChart x).symm q).1 (geodesic ((stateChart x).symm q) 1) = ‖((stateChart x).symm q).2‖ := by
    rw [hi,← exp_eq_geodesic]
    exact injectivity_subset_minimizing x hv
  have hgeom := (initialCost_geometry x hv).1.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hg : ContDiffAt ℝ 2 (initialCost x ((chartAt (Model n) y).symm (crossFlowCoordinates x y 1 q).1)) q.1 := by
    rw [hY]
    exact hgeom
  have ht := generatingHessian_cost_trial x y hε hε₁ hq hm hg (tangentChartLinear x ξ,α•κ)
  rw [hY] at ht
  change _ + lowerChristoffel _ _ _ _ ≤ _
  exact add_le_add ht le_rfl

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
