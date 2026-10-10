import OAI.Geometry.NodalSets.Charts.BaseChartFlux
import OAI.Geometry.NodalSets.Charts.CenteredSphereMetricLemmas

namespace OAI

namespace Yau.Target
open Manifold Matrix
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma sphereChartDerivative_stereo (p : Base) (y v : BaseModel) :
    sphereChartDerivative p y v =
      fderiv ℝ (stereoInvFunAux (-(p:AmbientBase))) (centeredSphereIsometry p y)
        (centeredSphereIsometry p v) := by
  rw [sphereChartDerivative_eq_fderiv p (by rw [centeredSphereChart_target]; trivial),
    centeredSphereChart_inverse]
  have h := (((contDiff_stereoInvFunAux (v := -(p:AmbientBase)) (m := ∞)).differentiable
    (by simp) (centeredSphereIsometry p y)).hasFDerivAt).comp y
      (centeredSphereIsometry p).toContinuousLinearMap.hasFDerivAt
  exact congrArg (fun L : BaseModel →L[ℝ] AmbientBase ↦ L v) h.fderiv

lemma sphereChartDerivative_conformal (p : Base) (y u v : BaseModel) :
    ⟪sphereChartDerivative p y u,sphereChartDerivative p y v⟫ =
      (4/(‖y‖^2+4))^2*⟪u,v⟫ := by
  have hp : ⟪(p:AmbientBase),(p:AmbientBase)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have hn : ‖(p:AmbientBase)‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.property
    rw [hn,one_pow]
  have ho (v : BaseModel) : ⟪centeredSphereIsometry p v,(p:AmbientBase)⟫ = 0 :=
    (real_inner_comm _ _).trans (centeredSphereIsometry_orthogonal p v)
  rw [sphereChartDerivative_stereo,sphereChartDerivative_stereo,
    stereoInvFunAux_fderiv,stereoInvFunAux_fderiv]
  simp only [stereoReciprocal,stereoNumerator,
    (centeredSphereIsometry p).norm_map,(centeredSphereIsometry p).inner_map_map,
    inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    inner_neg_left,inner_neg_right,ho,
    real_inner_comm (centeredSphereIsometry p y) (p:AmbientBase),
    real_inner_comm (centeredSphereIsometry p v) (p:AmbientBase),hp]
  simp only [real_inner_self_eq_norm_sq,real_inner_comm u y,real_inner_comm v y]
  have hd : ‖y‖^2+4 ≠ 0 := by positivity
  field_simp
  ring

lemma sphereRoundChartMatrix_conformal (p : Base) (y : BaseModel) :
    sphereRoundChartMatrix p y = (4/(‖y‖^2+4))^2 • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  rw [sphereRoundChartMatrix_inner,sphereChartDerivative_conformal]
  rw [(EuclideanSpace.basisFun (Fin 4) ℝ).inner_eq_ite]
  simp [Matrix.one_apply,mul_ite]

lemma sphereRoundChartMatrix_inverse_conformal (p : Base) (y : BaseModel) :
    (sphereRoundChartMatrix p y)⁻¹ = ((4/(‖y‖^2+4))^2)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  let : Invertible ((4/(‖y‖^2+4))^2) := invertibleOfNonzero (by positivity)
  rw [sphereRoundChartMatrix_conformal,Matrix.inv_smul (A := (1 : Matrix (Fin 4) (Fin 4) ℝ)) ((4/(‖y‖^2+4))^2) (by simp)]
  simp

lemma roundChartDensity_conformal (p : Base) (y : BaseModel) :
    roundChartDensity p y = (4/(‖y‖^2+4))^4 := by
  rw [roundChartDensity,sphereRoundChartMatrix_conformal,Matrix.det_smul]
  simp only [Fintype.card_fin,Matrix.det_one,mul_one]
  have h : ((4/(‖y‖^2+4))^2)^4 = ((4/(‖y‖^2+4))^4)^2 := by ring
  rw [h,Real.sqrt_sq (by positivity)]

end
end Yau.Target

end OAI
