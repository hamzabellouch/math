import OAI.Geometry.Relativity.CKS.SchwarzschildMetric
import OAI.Geometry.Relativity.CKS.InducedMetric

namespace OAI

noncomputable section
open Manifold Bundle Set Filter CKSLorentz CKSMetricGluing CKSSpatialManifold
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
local instance schwarzschildRoundMetricFinrank : Fact (Module.finrank ℝ E3 = 2+1) := ⟨by simp⟩

def euclideanMetric : ContMDiffRiemannianMetric 𝓘(ℝ,E3) ∞ E3 (fun x : E3 => TangentSpace 𝓘(ℝ,E3) x) :=
  { riemannianMetricVectorSpace E3 with contMDiff := (riemannianMetricVectorSpace E3).contMDiff.of_le le_top }

def sphereMetric : ContMDiffRiemannianMetric I2 ∞ E2 (fun x : Sphere => TangentSpace I2 x) :=
  CKSInducedArea.inducedMetric euclideanMetric (Subtype.val : Sphere → E3)
    (contMDiff_coe_sphere (n := 2)) (by
      intro point
      convert! injective_mvfderiv_subtypeVal_sphere (n := 2) point)

def sphereDerivative (n : Sphere) : E2 →L[ℝ] E3 := by
  exact mfderiv I2 𝓘(ℝ,E3) (Subtype.val : Sphere → E3) n
lemma sphereMetric_apply (n : Sphere) (v w : E2) :
    sphereMetric.inner n v w = ⟪sphereDerivative n v,sphereDerivative n w⟫_ℝ := rfl

lemma radialUnit_position {m : ℝ} (hm : 0 < m) (p : Exterior) :
    radialUnit (position m p) = directionAmbient p := by
  rw [radialUnit,norm_position hm,position,smul_smul,inv_mul_cancel₀ (ne_of_gt (radius_pos hm p)),one_smul]
lemma position_radial_inner {m : ℝ} (hm : 0 < m) (p : Exterior) (v : E3) :
    ⟪radialUnit (position m p),ambientDerivative (position m) p v⟫_ℝ = v 0 := by
  have ho : ⟪directionAmbient p,ambientDerivative directionAmbient p v⟫_ℝ = 0 := directionAmbient_orthogonal p v
  rw [radialUnit_position hm,mfderiv_position,inner_add_right,inner_smul_right,inner_smul_right,ho,
    real_inner_self_eq_norm_sq,norm_direction]
  ring

lemma metricInner_quad {m : ℝ} (hm : 0 < m) (p : Exterior) (v : E3) :
    metricInner m p v v = (v 0)^2 / lapseSquared m (radius m p) +
      (radius m p)^2 * ‖ambientDerivative directionAmbient p v‖^2 := by
  change cartMetric m (position m p) (ambientDerivative (position m) p v)
    (ambientDerivative (position m) p v) = _
  rw [cartMetric_apply,position_radial_inner hm,norm_position hm]
  have ho : ⟪ambientDerivative directionAmbient p v,directionAmbient p⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact directionAmbient_orthogonal p v
  rw [mfderiv_position,inner_add_left,inner_add_right,inner_add_right]
  have ho' : ⟪directionAmbient p,ambientDerivative directionAmbient p v⟫_ℝ = 0 :=
    directionAmbient_orthogonal p v
  simp only [inner_smul_left,inner_smul_right,ho,ho',starRingEnd_apply,star_trivial,
    real_inner_self_eq_norm_sq,norm_direction]
  ring

lemma angular_metric_bound {m : ℝ} (hm : 0 < m) (p : Exterior) (v : E3) :
    (2*m)^2 * sphereMetric.inner (angular p) (mfderiv I3 I2 angular p v)
      (mfderiv I3 I2 angular p v) ≤ metricInner m p v v := by
  have hs : sphereMetric.inner (angular p) (mfderiv I3 I2 angular p v)
      (mfderiv I3 I2 angular p v) = ‖ambientDerivative directionAmbient p v‖^2 := by
    have ha : (mfderiv I3 I2 angular p : E3 →L[ℝ] E2) = dropPlane := mfderiv_angular p
    have hd : ambientDerivative directionAmbient p = (sphereDerivative p.2).comp dropPlane :=
      mfderiv_directionAmbient p
    change ⟪sphereDerivative p.2 ((mfderiv I3 I2 angular p : E3 →L[ℝ] E2) v),
      sphereDerivative p.2 ((mfderiv I3 I2 angular p : E3 →L[ℝ] E2) v)⟫_ℝ = _
    rw [ha,hd,ContinuousLinearMap.comp_apply,real_inner_self_eq_norm_sq]
    rfl
  rw [hs,metricInner_quad hm]
  have hr := radius_ge m p
  have hm' : 0 ≤ 2*m := by positivity
  have hrad : (2*m)^2 ≤ (radius m p)^2 := sq_le_sq₀ hm' (radius_pos hm p).le |>.mpr hr
  have hmul := mul_le_mul_of_nonneg_right hrad (sq_nonneg ‖ambientDerivative directionAmbient p v‖)
  have hnn := div_nonneg (sq_nonneg (v 0)) (lapseSquared_pos hm (radius_ge m p)).le
  linarith

end CKSSchwarzschild

end

end OAI
