import OAI.Geometry.Relativity.CKS.LocalMaximumHessian
import OAI.Geometry.Relativity.CKS.SurfaceFrames
import OAI.Geometry.Relativity.CKS.SurfaceNormal
import OAI.Geometry.Relativity.CKS.SurfaceChristoffel

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma scalar_second_form_bound {r u h : ℝ} (hr : 0 < r) (hu : 0 < u) (hh : h ≤ -1) :
    u/r ≤ -(h/r/u + (1/u-u)/r) := by
  have he : -(h/r/u + (1/u-u)/r) - u/r = (-h-1)/(r*u) := by
    field_simp
    ring
  have := div_nonneg (by linarith : 0 ≤ -h-1) (mul_pos hr hu).le
  rw [← he] at this
  linarith

lemma outward_surface_second_form_bound {m : ℝ} (hm : 0 < m)
    {f : E2 → E3} {y : E2} (hf : ContDiffAt ℝ ∞ f y)
    (hmax : IsLocalMax (fun z => ‖f z‖^2) y) (hr : 2*m ≤ ‖f y‖)
    (a : E2) (ha : cartMetric m (f y) (fderiv ℝ f y a) (fderiv ℝ f y a) = 1) :
    lapse m ‖f y‖ / ‖f y‖ ≤ parameterSecondForm m f y (radialNormal m (f y)) a a := by
  have ht := maximum_radius_tangent (hf.differentiableAt (by simp)) hmax a
  have hau : ⟪fderiv ℝ f y a,fderiv ℝ f y a⟫_ℝ = 1 := by
    rwa [cartMetric_tangent m _ _ _ ht] at ha
  have hh := maximum_radius_hessian hf hmax a
  rw [hau] at hh
  have hs : ⟪radialUnit (f y),fderiv ℝ (fun z => fderiv ℝ f z a) y a⟫_ℝ =
      ⟪f y,fderiv ℝ (fun z => fderiv ℝ f z a) y a⟫_ℝ / ‖f y‖ := by
    simp only [radialUnit,real_inner_smul_left,div_eq_mul_inv]
    ring
  rw [parameterSecondForm,metric_normal_pair hm hr,christoffel_tangent_radial hm hr _ _ ht ht,hau,mul_one,hs]
  exact scalar_second_form_bound (lt_of_lt_of_le (by positivity) hr) (lapse_pos hm hr) hh

lemma outward_surface_mean_bound {m : ℝ} (hm : 0 < m)
    {f : E2 → E3} {y : E2} (hf : ContDiffAt ℝ ∞ f y)
    (hmax : IsLocalMax (fun z => ‖f z‖^2) y) (hr : 2*m ≤ ‖f y‖)
    (hinj : Function.Injective (fderiv ℝ f y)) :
    2*lapse m ‖f y‖/‖f y‖ ≤ parameterMeanCurvature m f y (radialNormal m (f y)) := by
  have hpos := cartMetric_pos hm hr
  have ha := outward_surface_second_form_bound hm hf hmax hr _ (firstFrame_unit _ _ hpos hinj)
  have hb := outward_surface_second_form_bound hm hf hmax hr _ (secondFrame_unit _ _ hpos hinj)
  dsimp [parameterMeanCurvature]
  calc
    2*lapse m ‖f y‖/‖f y‖ = lapse m ‖f y‖/‖f y‖ + lapse m ‖f y‖/‖f y‖ := by ring
    _ ≤ _ := add_le_add ha hb

lemma tangent_surface_tensor_trace {m : ℝ} (hm : 0 < m)
    {f : E2 → E3} {y : E2} (hf : DifferentiableAt ℝ f y)
    (hmax : IsLocalMax (fun z => ‖f z‖^2) y) (hr : 2*m ≤ ‖f y‖)
    (hinj : Function.Injective (fderiv ℝ f y)) :
    parameterTensorTrace m f y = 2*velocity m ‖f y‖/‖f y‖ := by
  have hpos := cartMetric_pos hm hr
  have ha := firstFrame_unit _ _ hpos hinj
  have hb := secondFrame_unit _ _ hpos hinj
  have hta := maximum_radius_tangent hf hmax (firstFrame (cartMetric m (f y)) (fderiv ℝ f y))
  have htb := maximum_radius_tangent hf hmax (secondFrame (cartMetric m (f y)) (fderiv ℝ f y))
  rw [cartMetric_tangent m _ _ _ hta] at ha
  rw [cartMetric_tangent m _ _ _ htb] at hb
  dsimp [parameterTensorTrace]
  rw [cartTensor_tangent m _ _ _ hta,cartTensor_tangent m _ _ _ htb,ha,hb]
  ring

end CKSSchwarzschild

end

end OAI
