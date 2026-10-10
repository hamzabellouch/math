import OAI.Geometry.Relativity.CKS.SchwarzschildCartesianDerivatives

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma radialUnit_inner_self {x : E3} (hx : x ≠ 0) : ⟪radialUnit x,radialUnit x⟫_ℝ = 1 := by
  rw [real_inner_self_eq_norm_sq,norm_radialUnit hx,one_pow]
lemma tangentProjection_orthogonal {x : E3} (hx : x ≠ 0) (a : E3) :
    ⟪radialUnit x,tangentProjection x a⟫_ℝ = 0 := by
  simp [tangentProjection,inner_sub_right,inner_smul_right,norm_radialUnit hx]
lemma cartMetric_tangent (m : ℝ) (x a b : E3) (ha : ⟪radialUnit x,a⟫_ℝ = 0) :
    cartMetric m x a b = ⟪a,b⟫_ℝ := by simp [cartMetric_apply,ha]
lemma cartTensor_tangent (m : ℝ) (x a b : E3) (ha : ⟪radialUnit x,a⟫_ℝ = 0) :
    cartTensor m x a b = velocity m ‖x‖ / ‖x‖ * ⟪a,b⟫_ℝ := by
  simp [cartTensor,euclideanForm_apply,radialForm_apply,ha]

lemma radial_connection_tangent {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖)
    (a b : E3) (ha : ⟪radialUnit x,a⟫_ℝ = 0) (hb : ⟪radialUnit x,b⟫_ℝ = 0) :
    covariantPair (cartMetric m) (radialNormal m) x a b = lapse m ‖x‖/‖x‖ * ⟪a,b⟫_ℝ := by
  have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hr)
  let c := fun y : E3 => (lapseSquared m ‖y‖)⁻¹-1
  have hc : DifferentiableAt ℝ c x := by
    exact ((((lapseSquared_smoothAt (lt_of_lt_of_le (by positivity) hr)).comp x
      (contDiffAt_norm ℝ hx)).inv (ne_of_gt (lapseSquared_pos hm hr))).sub contDiffAt_const).differentiableAt (by simp)
  have hn : fderiv ℝ (radialNormal m) x a = (lapse m ‖x‖/‖x‖) • a := by
    rw [radialNormal_derivative hm hr,ha]
    simp [tangentProjection,ha]
  unfold covariantPair
  rw [hn]
  change cartMetric m x ((lapse m ‖x‖/‖x‖) • a) b + 1/2 *
    (fderiv ℝ (fun y => ⟪radialNormal m x,b⟫_ℝ + c y * (⟪radialUnit y,radialNormal m x⟫_ℝ * ⟪radialUnit y,b⟫_ℝ)) x a +
     fderiv ℝ (fun y => ⟪a,b⟫_ℝ + c y * (⟪radialUnit y,a⟫_ℝ * ⟪radialUnit y,b⟫_ℝ)) x (radialNormal m x) -
     fderiv ℝ (fun y => ⟪a,radialNormal m x⟫_ℝ + c y * (⟪radialUnit y,a⟫_ℝ * ⟪radialUnit y,radialNormal m x⟫_ℝ)) x b) = _
  rw [radial_metric_derivative hx c hc,radial_metric_derivative hx c hc,radial_metric_derivative hx c hc]
  simp only [ha,hb,zero_mul,mul_zero,sub_zero,zero_add,add_zero]
  rw [cartMetric_apply]
  simp only [inner_smul_right,real_inner_smul_left,ha,hb,mul_zero,add_zero,
    radialNormal,radialUnit_inner_self hx,mul_one]
  rw [real_inner_comm b a]
  ring

lemma tangentProjection_normSq {x : E3} (hx : x ≠ 0) (a : E3) :
    ⟪tangentProjection x a,tangentProjection x a⟫_ℝ = ⟪a,a⟫_ℝ - ⟪radialUnit x,a⟫_ℝ^2 := by
  simp only [tangentProjection,inner_sub_left,inner_sub_right,real_inner_smul_left,inner_smul_right,
    radialUnit_inner_self hx,real_inner_comm a (radialUnit x)]
  ring

lemma sphereMeanCurvature_eq {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) :
    sphereMeanCurvature m x = 2*lapse m ‖x‖/‖x‖ := by
  have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hr)
  unfold sphereMeanCurvature
  simp_rw [radial_connection_tangent hm hr _ _ (tangentProjection_orthogonal hx _) (tangentProjection_orthogonal hx _)]
  rw [← Finset.mul_sum]
  have hs : (∑ i : Fin 3, ⟪tangentProjection x (EuclideanSpace.single i 1),tangentProjection x (EuclideanSpace.single i 1)⟫_ℝ) = 2 := by
    simp_rw [tangentProjection_normSq hx]
    rw [Finset.sum_sub_distrib]
    simp only [EuclideanSpace.inner_single_right,one_mul,PiLp.single_apply,ite_true]
    have h := real_inner_self_eq_norm_sq (radialUnit x)
    change (∑ i : Fin 3, (radialUnit x) i * (radialUnit x) i) = ‖radialUnit x‖^2 at h
    rw [norm_radialUnit hx] at h
    simp only [one_pow] at h
    simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
    simp only [starRingEnd_apply,star_trivial,← sq] at h ⊢
    linarith
  rw [hs]
  ring

lemma sphereTensorTrace_eq {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) :
    sphereTensorTrace m x = 2*velocity m ‖x‖/‖x‖ := by
  have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hr)
  unfold sphereTensorTrace
  simp_rw [cartTensor_tangent m x _ _ (tangentProjection_orthogonal hx _)]
  have he := sphereMeanCurvature_eq hm hr
  unfold sphereMeanCurvature at he
  simp_rw [radial_connection_tangent hm hr _ _ (tangentProjection_orthogonal hx _) (tangentProjection_orthogonal hx _)] at he
  rw [← Finset.mul_sum] at he ⊢
  have hp := lapse_pos hm hr
  have hn : 0 < ‖x‖ := lt_of_lt_of_le (by positivity) hr
  have hs : (∑ i : Fin 3, ⟪tangentProjection x (EuclideanSpace.single i 1),tangentProjection x (EuclideanSpace.single i 1)⟫_ℝ) = 2 := by
    apply (mul_left_cancel₀ (ne_of_gt (div_pos hp hn)))
    rw [he]
    ring
  rw [hs]
  ring

theorem horizon_expansion {m : ℝ} (hm : 0 < m) {x : E3} (hx : ‖x‖ = 2*m) :
    sphereThetaPlus m x = 0 := by
  unfold sphereThetaPlus
  rw [sphereMeanCurvature_eq hm (by linarith),sphereTensorTrace_eq hm (by linarith),hx,
    lapse_horizon hm,velocity_near m (2*m) (by linarith)]
  ring
end CKSSchwarzschild

end

end OAI
