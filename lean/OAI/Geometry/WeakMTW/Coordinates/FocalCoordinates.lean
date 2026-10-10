import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.FibreNonfocal
import OAI.Geometry.WeakMTW.Variations.ActionHessian
import OAI.Geometry.WeakMTW.Variations.GeneratingAction
import OAI.Geometry.WeakMTW.Geodesics.GaussGlobal

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry DiscreteVariational
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]

 def verticalCoordinates (x : M) (v : TangentSpace (model n) x) : Model n × Model n :=
   (chartAt (Model n) x x,tangentChartLinear x v)

 theorem verticalCoordinates_eq (x : M) (v : TangentSpace (model n) x) :
    verticalCoordinates x v = stateChart x (⟨x,v⟩ : TangentBundle (model n) M) := by
  apply Prod.ext
  · rfl
  · exact tangentChartLinear_eq x v

variable [RiemannianBundle (fun x : M => TangentSpace (model n) x)]

omit [IsManifold (model n) ∞ M] in
 theorem verticalCoordinates_smooth (x : M) : ContDiff ℝ ∞ (verticalCoordinates (n := n) x) := by
   unfold verticalCoordinates
   exact contDiff_const.prodMk (tangentChartLinear (n := n) x).contDiff

variable [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem crossFlowCoordinates_vertical (x y : M) (v : TangentSpace (model n) x) :
    (crossFlowCoordinates x y 1 (verticalCoordinates x v)).1 = chartAt (Model n) y (exp x v) := by
  have hp : (⟨x,v⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  rw [verticalCoordinates_eq]
  dsimp only [crossFlowCoordinates]
  rw [(stateChart x).left_inv hp]
  change chartAt (Model n) y (geodesic (⟨x,v⟩ : TangentBundle (model n) M) 1) = _
  rw [← exp_eq_geodesic]

 theorem fibre_kernel_state_kernel (x y : M) {v k : TangentSpace (model n) x}
    (hy : exp x v ∈ (chartAt (Model n) y).source)
    (hk : fderiv ℝ (fun w => chartAt (Model n) y (exp x w)) v k = 0) :
    fderiv ℝ (fun q => (crossFlowCoordinates x y 1 q).1) (verticalCoordinates x v)
      (0,tangentChartLinear x k) = 0 := by
  have hp : (⟨x,v⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  have hq : verticalCoordinates x v ∈ (stateChart x).target := by
    rw [verticalCoordinates_eq]; exact (stateChart x).map_source hp
  have hys : geodesicFlow 1 ((stateChart x).symm (verticalCoordinates x v)) ∈ (stateChart y).source := by
    rw [verticalCoordinates_eq,(stateChart x).left_inv hp]
    apply (stateChart_source y _).mpr
    change geodesic (⟨x,v⟩ : TangentBundle (model n) M) 1 ∈ _
    simpa only [← exp_eq_geodesic] using hy
  have hD := ((chart_flow_smooth x y 1 hq hys).fst.differentiableAt (by simp)).hasFDerivAt
  have hV : HasFDerivAt (verticalCoordinates (n := n) x)
      ((0 : TangentSpace (model n) x →L[ℝ] Model n).prod (tangentChartLinear x)) v :=
    (hasFDerivAt_const (chartAt (Model n) x x) v).prodMk (tangentChartLinear x).hasFDerivAt
  have hd := hD.comp v hV
  have hd' : HasFDerivAt (fun w => chartAt (Model n) y (exp x w))
      ((fderiv ℝ (fun q => (crossFlowCoordinates x y 1 q).1) (verticalCoordinates x v)).comp
        ((0 : TangentSpace (model n) x →L[ℝ] Model n).prod (tangentChartLinear x))) v := by
    convert! hd using 1
    funext w
    exact (crossFlowCoordinates_vertical x y w).symm
  have he := congrArg (fun A : TangentSpace (model n) x →L[ℝ] Model n => A k) hd'.fderiv
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,zero_apply,hk] using he.symm

 theorem fibre_kernel_perp_radial (x y : M) {v k : TangentSpace (model n) x}
    (hy : exp x v ∈ (chartAt (Model n) y).source)
    (hk : fderiv ℝ (fun w => chartAt (Model n) y (exp x w)) v k = 0) :
    inner ℝ k v = 0 := by
  let P : ℝ → TangentBundle (model n) M := fun s => ⟨x,v+s•k⟩
  have hp₀ : P 0 = (⟨x,v⟩ : TangentBundle (model n) M) := by simp [P]
  have hys : (1,0) ∈ fanDomain y P := by
    apply (stateChart_source y _).mpr
    change geodesic (P 0) 1 ∈ _
    simpa only [hp₀,← exp_eq_geodesic] using hy
  have hd : HasDerivAt (fun s : ℝ => v+s•k) k 0 := by
    convert! (hasDerivAt_const (0 : ℝ) v).add ((hasDerivAt_id (0 : ℝ)).smul_const k) using 1
    simp
  have hF := ((exp_coordinates_smooth x y hy).differentiableAt (by simp)).hasFDerivAt
  have hF' : HasFDerivAt (fun w => chartAt (Model n) y (exp x w))
      (fderiv ℝ (fun w => chartAt (Model n) y (exp x w)) v) (v+(0 : ℝ)•k) := by simpa using hF
  have hh := hF'.comp_hasDerivAt (l := fun w => chartAt (Model n) y (exp x w))
    (f := fun s : ℝ => v+s•k) 0 hd
  rw [hk] at hh
  have hc : HasDerivAt (fun s => (fanCoordinates y P (1,s)).1) 0 0 := by
    convert! hh using 1
    funext s
    change chartAt (Model n) y (geodesic (P s) 1) = _
    rw [← exp_eq_geodesic]
    rfl
  have hm := fanMomentum_coord_deriv y (vertical_fan_smooth x v k) hys
  rw [hc.deriv,map_zero] at hm
  have hgauss := vertical_fan_momentum x v k 1
  change fanMomentum P 1 = 1*inner ℝ v k at hgauss
  rw [hm,one_mul,real_inner_comm] at hgauss
  exact hgauss.symm

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
