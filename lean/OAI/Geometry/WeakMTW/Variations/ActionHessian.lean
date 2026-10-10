import Mathlib
import OAI.Geometry.WeakMTW.Variations.BranchInitialGeometry
import OAI.Geometry.WeakMTW.Variations.GeodesicSecondCoordinates
import OAI.Geometry.WeakMTW.Variations.MTWConcavity

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def initialCost (x y : M) (a : Model n) : ℝ := cost ((chartAt (Model n) x).symm a) y

 def tangentChartLinear (x : M) : TangentSpace (model n) x →L[ℝ] Model n :=
   mfderiv (model n) (model n) (chartAt (Model n) x) x

omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem tangentChartLinear_eq (x : M) (v : TangentSpace (model n) x) :
    tangentChartLinear x v = (stateChart x (⟨x,v⟩ : TangentBundle (model n) M)).2 := by
  have hh := congrArg (fun p : TangentBundle (model n) (Model n) => p.2)
    (tangentMap_chart (p := (⟨x,0⟩ : TangentBundle (model n) M))
      (q := (⟨x,v⟩ : TangentBundle (model n) M)) (mem_chart_source (Model n) x))
  exact hh

 theorem initialCost_geometry (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) :
    ContDiffAt ℝ ∞ (initialCost x (exp x v)) (chartAt (Model n) x x) ∧
    (∀ w, fderiv ℝ (initialCost x (exp x v)) (chartAt (Model n) x x) w =
      -metric x (chartAt (Model n) x x) (tangentChartLinear x v) w) ∧
    (∀ w, actionForm (metric x) (initialCost x (exp x v)) (chartAt (Model n) x x)
      (tangentChartLinear x v) w (tangentChartLinear x v) =
        metric x (chartAt (Model n) x x) w (tangentChartLinear x v)) := by
  let y := exp x v
  let c := chartAt (Model n) x
  let d := chartAt (Model n) y
  let q : Model n × Model n := (c x,d y)
  obtain ⟨e,he,hev,hes,hei⟩ := pairExpCoordinates_local_inverse x y hv (mem_chart_source (Model n) y)
  have heq : e (stateChart x (⟨x,v⟩ : TangentBundle (model n) M)) = q := by
    rw [he,pairExpCoordinates_vertical]
  have hq : q ∈ e.target := heq ▸ e.map_source hev
  have hiv : e.symm q = stateChart x (⟨x,v⟩ : TangentBundle (model n) M) := by
    rw [← heq,e.left_inv hev]
  have hEq : initialCost x y =ᶠ[𝓝 q.1] (fun a => branchAction x e (a,q.2)) := by
    have hmap : ContinuousAt (fun a : Model n => (a,q.2)) q.1 := continuousAt_id.prodMk continuousAt_const
    have h := hmap.tendsto (cost_coord_eq_interior_inverse x hv e he hev)
    filter_upwards [h] with a ha
    change cost (c.symm a) (d.symm (d y)) = _ at ha
    rw [d.left_inv (mem_chart_source (Model n) y)] at ha
    exact ha
  have hf := branch_initial_smooth x y e hes hei hq
  refine ⟨hf.congr_of_eventuallyEq hEq,?_,?_⟩
  · intro w
    rw [hEq.fderiv_eq,branch_initial_gradient x y e he hes hei hq w,hiv,tangentChartLinear_eq]
  · intro w
    have hdf : fderiv ℝ (initialCost x y) =ᶠ[𝓝 q.1]
        fderiv ℝ (fun a => branchAction x e (a,q.2)) := hEq.fderiv
    have hdd : fderiv ℝ (fderiv ℝ (initialCost x y)) q.1 =
        fderiv ℝ (fderiv ℝ (fun a => branchAction x e (a,q.2))) q.1 := hdf.fderiv_eq
    have hh := branch_initial_radial x y e he hes hei hq w
    rw [hiv,← tangentChartLinear_eq] at hh
    change fderiv ℝ (fderiv ℝ (initialCost x y)) q.1 w (tangentChartLinear x v) + _ = _
    rw [hdd]
    exact hh

 def actionHessian (x : M) (v : TangentSpace (model n) x) :
    LinearMap.BilinForm ℝ (TangentSpace (model n) x) :=
  (actionForm (metric x) (initialCost x (exp x v)) (chartAt (Model n) x x)
    (tangentChartLinear x v)).compl₁₂ (tangentChartLinear x).toLinearMap (tangentChartLinear x).toLinearMap

 theorem actionHessian_symmetric (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) (ξ η : TangentSpace (model n) x) :
    actionHessian x v ξ η = actionHessian x v η ξ := by
  exact actionForm_symmetric (metric x) (initialCost x (exp x v)) (chartAt (Model n) x).open_target
    ((metric_smooth x).differentiableOn (by simp)) (fun a _ => metric_symmetric x a)
    ((chartAt (Model n) x).map_source (mem_chart_source (Model n) x))
    ((initialCost_geometry x hv).1.of_le (by simp))
    (tangentChartLinear x v) (tangentChartLinear x ξ) (tangentChartLinear x η)

 theorem actionHessian_radial (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) (ξ : TangentSpace (model n) x) :
    actionHessian x v ξ v = inner ℝ ξ v := by
  change actionForm _ _ _ _ (tangentChartLinear x ξ) (tangentChartLinear x v) = _
  rw [(initialCost_geometry x hv).2.2]
  exact metric_chart_pair x x (mem_chart_source (Model n) x) ξ v

 theorem actionHessian_diag (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) (ξ : TangentSpace (model n) x) :
    actionHessian x v ξ ξ = actionHessianDiag x v ξ := by
  let f : Model n → ℝ := initialCost x (exp x v)
  let a := chartAt (Model n) x x
  let u := tangentChartLinear x ξ
  have hgeom := initialCost_geometry x hv
  have hh := chart_geodesic_second x ξ f
    (hgeom.1.of_le (by simp))
  rw [← tangentChartLinear_eq] at hh
  have he : (fun t : ℝ => f (chartAt (Model n) x (exp x (t • ξ)))) =ᶠ[𝓝 0]
      (fun t : ℝ => cost (exp x (t • ξ)) (exp x v)) := by
    have hcont : ContinuousAt (fun t : ℝ => exp x (t • ξ)) 0 :=
      (exp_fibre_smooth x).continuous.continuousAt.comp (continuousAt_id.smul continuousAt_const)
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, exp x (t•ξ) ∈ (chartAt (Model n) x).source := by
      apply hcont.preimage_mem_nhds
      simpa only [zero_smul,exp_zero] using (chartAt (Model n) x).open_source.mem_nhds (mem_chart_source (Model n) x)
    filter_upwards [hnear] with t ht
    exact congrArg (fun z => cost z (exp x v)) ((chartAt (Model n) x).left_inv ht)
  rw [he.deriv.deriv_eq] at hh
  change actionForm (metric x) f a (tangentChartLinear x v) u u = _
  rw [actionForm_eq (metric x) f a (tangentChartLinear x v) u u
    (fun z hz => metric_positive x ((chartAt (Model n) x).map_source (mem_chart_source (Model n) x)) hz)
    (metric_symmetric x a)]
  rw [hgeom.2.1] at hh
  change actionHessianDiag x v ξ = _ at hh
  linarith

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
