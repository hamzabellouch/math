import OAI.Geometry.Relativity.CKS.SphereConeChart

namespace OAI

noncomputable section
open Set Filter CKSLorentz CKSCalculus CKSRealizedRound CKSAngularGeometry CKSCartesianOuter
open CKSSphericalChart
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma inner_pair_one (v w : E3) : ⟪v,w⟫_ℝ = pair (1 : AmbientMat) v w := by
  rw [pair_one]
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  apply Finset.sum_congr rfl
  intro i _
  ring
lemma radialUnit_spherical {x : PhysicalPoint} (hr : 0 < x 0) :
    radialUnit (toPoint.symm (sphericalMap x)) = CKSSphericalChart.sphereParam x := by
  rw [radialUnit,sphericalMap_norm hr,sphericalMap_euclidean,smul_smul,
    inv_mul_cancel₀ hr.ne',one_smul]
lemma round_lapse_eq (m : ℝ) (x : PhysicalPoint) :
    CKSRealizedRound.lapse (fun _ => m) (velocity m) x = lapse m (x 0) := by
  unfold CKSRealizedRound.lapse CKSRealizedRound.radicand CKSRealizedRound.radial
    lapse lapseSquared
  congr 1
  ring
lemma round_radicand_eq (m : ℝ) (x : PhysicalPoint) :
    CKSRealizedRound.radicand (fun _ => m) (velocity m) x = lapseSquared m (x 0) := by
  unfold CKSRealizedRound.radicand CKSRealizedRound.radial lapseSquared
  ring
lemma spherical_metric_pullback {m : ℝ} {x : PhysicalPoint} (hr : 0 < x 0)
    (hp : 0 < lapseSquared m (x 0)) :
    coordinatePullback sphericalMap (spatialCoefficients (cartMetric m)) x =
      outerMetric (fun _ => m) (velocity m) x := by
  ext i j
  unfold coordinatePullback
  rw [spatialCoefficients_pair,sphericalMap_fderiv,sphericalMap_fderiv,
    toPoint.symm_apply_apply,toPoint.symm_apply_apply,cartMetric_apply,
    sphericalMap_norm hr,radialUnit_spherical hr,inner_pair_one,pair_one_sphericalBasis]
  have h (i : Fin 3) : ⟪CKSSphericalChart.sphereParam x,sphericalBasis x i⟫_ℝ = if i=0 then 1 else 0 := by
    rw [inner_pair_one,pair_one]
    exact normalDot_sphericalBasis x i
  rw [h,h]
  have hu : (CKSRealizedRound.lapse (fun _ => m) (velocity m) x)^2 = lapseSquared m (x 0) := by
    rw [round_lapse_eq,lapse,Real.sq_sqrt hp.le]
  change _ = (Matrix.diagonal ![1/(CKSRealizedRound.lapse (fun _ => m) (velocity m) x)^2,
    x 0^2,x 0^2*Real.sin (x 1)^2]) i j
  rw [hu]
  fin_cases i <;> fin_cases j <;> simp [sphericalScale,Matrix.diagonal,div_eq_mul_inv]
  ring
lemma spherical_tensor_pullback {m : ℝ} {x : PhysicalPoint} (hr : 0 < x 0)
    (hp : 0 < lapseSquared m (x 0)) :
    coordinatePullback sphericalMap (spatialCoefficients (cartTensor m)) x =
      tensor (CKSRealizedRound.lapse (fun _ => m) (velocity m)) (velocity m)
        (radial (deriv (velocity m))) (fun _ => 0) (fun _ => 0) x := by
  ext i j
  unfold coordinatePullback
  rw [spatialCoefficients_pair,sphericalMap_fderiv,sphericalMap_fderiv,
    toPoint.symm_apply_apply,toPoint.symm_apply_apply]
  change velocity m ‖toPoint.symm (sphericalMap x)‖ / ‖toPoint.symm (sphericalMap x)‖ *
    ⟪sphericalBasis x i,sphericalBasis x j⟫_ℝ +
    (deriv (velocity m) ‖toPoint.symm (sphericalMap x)‖ / lapseSquared m ‖toPoint.symm (sphericalMap x)‖ -
      velocity m ‖toPoint.symm (sphericalMap x)‖ / ‖toPoint.symm (sphericalMap x)‖) *
    (⟪radialUnit (toPoint.symm (sphericalMap x)),sphericalBasis x i⟫_ℝ *
      ⟪radialUnit (toPoint.symm (sphericalMap x)),sphericalBasis x j⟫_ℝ) = _
  rw [sphericalMap_norm hr,radialUnit_spherical hr,inner_pair_one,pair_one_sphericalBasis]
  have h (i : Fin 3) : ⟪CKSSphericalChart.sphereParam x,sphericalBasis x i⟫_ℝ = if i=0 then 1 else 0 := by
    rw [inner_pair_one,pair_one]
    exact normalDot_sphericalBasis x i
  rw [h,h]
  have hu : (CKSRealizedRound.lapse (fun _ => m) (velocity m) x)^2 = lapseSquared m (x 0) := by
    rw [round_lapse_eq,lapse,Real.sq_sqrt hp.le]
  simp only [CKSRealizedRound.tensor,radial,hu]
  fin_cases i <;> fin_cases j <;> simp [sphericalScale] <;> field_simp
end CKSSchwarzschild

end

end OAI
