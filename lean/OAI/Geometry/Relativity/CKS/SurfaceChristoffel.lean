import OAI.Geometry.Relativity.CKS.SchwarzschildConnection
import OAI.Geometry.Relativity.CKS.SchwarzschildHorizonExclusionDefinitions

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma metric_normal_pair {m : ℝ} (hm : 0 < m) {x : E3} (hx : 2*m ≤ ‖x‖) (z : E3) :
    cartMetric m x (radialNormal m x) z = ⟪radialUnit x,z⟫_ℝ / lapse m ‖x‖ := by
  have hxn : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hx)
  have hu := lapse_pos hm hx
  rw [cartMetric_apply]
  simp only [radialNormal,real_inner_smul_left,inner_smul_right,radialUnit_inner_self hxn,mul_one]
  rw [← lapse_sq hm hx]
  field_simp
  ring

lemma christoffel_tangent_radial {m : ℝ} (hm : 0 < m) {x : E3} (hx : 2*m ≤ ‖x‖)
    (a b : E3) (ha : ⟪radialUnit x,a⟫_ℝ = 0) (hb : ⟪radialUnit x,b⟫_ℝ = 0) :
    christoffelPair (cartMetric m) x a b (radialNormal m x) =
      (1/lapse m ‖x‖ - lapse m ‖x‖) / ‖x‖ * ⟪a,b⟫_ℝ := by
  have hn : 0 < ‖x‖ := lt_of_lt_of_le (by positivity) hx
  have hxn : x ≠ 0 := norm_pos_iff.mp hn
  let c := fun y : E3 => (lapseSquared m ‖y‖)⁻¹-1
  have hc : DifferentiableAt ℝ c x :=
    ((((lapseSquared_smoothAt hn).comp x (contDiffAt_norm ℝ hxn)).inv
      (ne_of_gt (lapseSquared_pos hm hx))).sub contDiffAt_const).differentiableAt (by simp)
  unfold christoffelPair
  change 1/2 *
    (fderiv ℝ (fun y => ⟪b,radialNormal m x⟫_ℝ+c y*(⟪radialUnit y,b⟫_ℝ * ⟪radialUnit y,radialNormal m x⟫_ℝ)) x a +
     fderiv ℝ (fun y => ⟪a,radialNormal m x⟫_ℝ+c y*(⟪radialUnit y,a⟫_ℝ * ⟪radialUnit y,radialNormal m x⟫_ℝ)) x b -
     fderiv ℝ (fun y => ⟪a,b⟫_ℝ+c y*(⟪radialUnit y,a⟫_ℝ * ⟪radialUnit y,b⟫_ℝ)) x (radialNormal m x)) = _
  rw [radial_metric_derivative hxn c hc,radial_metric_derivative hxn c hc,
    radial_metric_derivative hxn c hc]
  simp only [ha,hb,zero_mul,mul_zero,zero_add,add_zero,sub_zero,
    radialNormal,inner_smul_right,real_inner_smul_left,radialUnit_inner_self hxn,mul_one]
  rw [real_inner_comm b a]
  dsimp [c]
  rw [← lapse_sq hm hx]
  have hu := lapse_pos hm hx
  field_simp
  ring

lemma christoffel_neg_normal (g : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ) (x a b N : E3) :
    christoffelPair g x a b (-N) = -christoffelPair g x a b N := by
  simp only [christoffelPair,map_neg,fderiv_fun_neg,neg_apply]
  ring
lemma parameterSecondForm_neg (m : ℝ) (f : E2 → E3) (y : E2) (N : E3) (a b : E2) :
    parameterSecondForm m f y (-N) a b = -parameterSecondForm m f y N a b := by
  simp only [parameterSecondForm,map_neg,neg_apply,christoffel_neg_normal]
  ring
lemma parameterMeanCurvature_neg (m : ℝ) (f : E2 → E3) (y : E2) (N : E3) :
    parameterMeanCurvature m f y (-N) = -parameterMeanCurvature m f y N := by
  simp only [parameterMeanCurvature,parameterSecondForm_neg]
  ring

end CKSSchwarzschild

end

end OAI
