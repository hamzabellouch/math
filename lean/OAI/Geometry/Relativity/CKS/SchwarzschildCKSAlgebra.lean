import OAI.Geometry.Relativity.CKS.SchwarzschildMetricDefinitions
import OAI.Geometry.Relativity.CKS.InducedMetric

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMixedGeometry CKSAngularSlice
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

def metricPerturbation (m : ℝ) : SpatialTensor := fun x => cartMetric m x - hyperbolicField x
def tensorPerturbation (m : ℝ) : SpatialTensor := fun x => cartTensor m x - hyperbolicField x
def radialCoefficient (m r : ℝ) : ℝ :=
  letI := CKSBoundarySurface.two_atLeastTwo
  (1+r^2-2*m/r)⁻¹-(1+r^2)⁻¹

lemma velocity_deriv_far (m r : ℝ) (hr : 2*m+2 < r) : deriv (velocity m) r = 1 := by
  have h : velocity m =ᶠ[𝓝 r] id := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact velocity_far m s hs.le
  rw [h.deriv_eq]
  exact deriv_id r
lemma cartTensor_far (m : ℝ) {x : E3} (hx : 2*m+2 < ‖x‖) (hp : 0 < ‖x‖) :
    cartTensor m x = cartMetric m x := by
  rw [cartTensor,cartMetric,velocity_far m ‖x‖ hx.le,velocity_deriv_far m ‖x‖ hx,
    div_self hp.ne',one_smul,one_div]
lemma hyperbolic_radial (x : E3) (hx : x ≠ 0) :
    hyperbolicField x = euclideanForm + ((1+‖x‖^2)⁻¹-1) • radialForm x := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hd : 1+‖x‖^2 ≠ 0 := by positivity
  change ⟪v,w⟫_ℝ - 1/(1+‖x‖^2)*(⟪x,v⟫_ℝ * ⟪x,w⟫_ℝ) =
    ⟪v,w⟫_ℝ + ((1+‖x‖^2)⁻¹-1)*(⟪‖x‖⁻¹ • x,v⟫_ℝ * ⟪‖x‖⁻¹ • x,w⟫_ℝ)
  simp only [real_inner_smul_left]
  field_simp
  ring
lemma metricPerturbation_far (m : ℝ) {x : E3} (hx : 2*m+2 ≤ ‖x‖) (hp : 0 < ‖x‖) :
    metricPerturbation m x = radialCoefficient m ‖x‖ • radialForm x := by
  rw [metricPerturbation,hyperbolic_radial x (norm_ne_zero_iff.mp hp.ne')]
  unfold cartMetric lapseSquared radialCoefficient
  rw [velocity_far m ‖x‖ hx]
  have he : 1-2*m/‖x‖+‖x‖^2 = 1+‖x‖^2-2*m/‖x‖ := by ring
  rw [he]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp only [add_apply,sub_apply,smul_apply,smul_eq_mul]
  ring

lemma radialUnit_polar (P : SmoothAngularPatch) {y : Point} (hr : 0 < y 0) :
    radialUnit (polarParam P y) = P.param (angularProjection y) := by
  rw [radialUnit,polarParam_norm P hr.le,polarParam,smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
lemma radial_dot_polar (P : SmoothAngularPatch) {y : Point} (hr : 0 < y 0)
    (hy : angularProjection y ∈ P.chart.target) (i : I) :
    ⟪radialUnit (polarParam P y), fderiv ℝ (polarParam P) y (basis i)⟫_ℝ =
      if i=0 then 1 else 0 := by
  rw [radialUnit_polar P hr]
  cases i using Fin.cases
  · rw [polarParam_fderiv_radial P hy,real_inner_self_eq_norm_sq]
    have hn : ‖P.param (angularProjection y)‖ = 1 := P.param_norm (angularProjection y)
    simp [hn]
  · rw [polarParam_fderiv_angular P hy,inner_smul_right,P.param_tangent hy]
    simp
lemma perturbation_polar (m : ℝ) (P : SmoothAngularPatch) {y : Point}
    (hr : 2*m+2 < y 0) (hp : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) (i k : I) :
    polarTensorComponents P (metricPerturbation m) i k y =
      (if i=0 ∧ k=0 then radialCoefficient m (y 0) else 0) ∧
    polarTensorComponents P (tensorPerturbation m) i k y =
      if i=0 ∧ k=0 then radialCoefficient m (y 0) else 0 := by
  have hn := polarParam_norm P hp.le
  have hM := metricPerturbation_far m (x := polarParam P y) (by rw [hn]; exact hr.le)
    (by rwa [hn])
  have hK : tensorPerturbation m (polarParam P y) = metricPerturbation m (polarParam P y) := by
    rw [tensorPerturbation,metricPerturbation,cartTensor_far m (by rwa [hn]) (by rwa [hn])]
  have he : polarTensorComponents P (metricPerturbation m) i k y =
      if i=0 ∧ k=0 then radialCoefficient m (y 0) else 0 := by
    unfold polarTensorComponents
    rw [hM,hn]
    change radialCoefficient m (y 0) *
      (⟪radialUnit (polarParam P y),fderiv ℝ (polarParam P) y (basis i)⟫_ℝ *
      ⟪radialUnit (polarParam P y),fderiv ℝ (polarParam P) y (basis k)⟫_ℝ) = _
    rw [radial_dot_polar P hp hy,radial_dot_polar P hp hy]
    split_ifs <;> simp_all
  exact ⟨he,by unfold polarTensorComponents; rw [hK]; exact he⟩
end CKSSchwarzschild

end

end OAI
