import OAI.Geometry.IsometricImmersion.Curvature.GaussConnection
import OAI.Geometry.IsometricImmersion.Immersions.NormalSpace

namespace OAI

noncomputable section
open scoped ContDiff BigOperators
namespace SmoothLocal.Geometry

theorem isometric_tangents_independent {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    {p : Coord} (hp : p ∈ U) : LinearIndependent ℝ (fun i => coordPartial i F p) := by
  simpa only [Function.comp_def, Pi.basisFun_apply, coordPartial,
    ContinuousLinearMap.coe_coe] using
    (Pi.basisFun ℝ (Fin 2)).linearIndependent.map' (fderiv ℝ F p).toLinearMap
      (LinearMap.ker_eq_bot_of_injective (isometricOn_injective_differential hg hF hp))

theorem normalResidual_eq_secondFundamental_smul {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) {n : Ambient}
    (hn : IsUnitNormalAt F n p) (i j : Fin 2) :
    normalResidual g F p i j = secondFundamental F n p i j • n := by
  have hnt (k : Fin 2) : inner ℝ (coordPartial k F p) n = 0 := hn.2 _
  have hwt (k : Fin 2) : inner ℝ (coordPartial k F p) (normalResidual g F p i j) = 0 := by
    rw [real_inner_comm]
    exact normalResidual_orthogonal_tangent hg hF hU hp i j k
  have hline := normal_eq_inner_smul_of_independent_tangents
    (fun k => coordPartial k F p) (isometric_tangents_independent hg hF hp)
    n (normalResidual g F p i j) hn.1 hnt hwt
  have hcoef : inner ℝ n (normalResidual g F p i j) = secondFundamental F n p i j := by
    rw [real_inner_comm]
    simp only [normalResidual, inner_sub_left, sum_inner, real_inner_smul_left,
      hnt, mul_zero, Finset.sum_const_zero, sub_zero, secondFundamental]
  rw [hcoef] at hline
  exact hline

theorem covHessian_height_eq_normal_mul_secondFundamental
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) {n : Ambient} (hn : IsUnitNormalAt F n p) (e : Ambient) :
    covHessian g (height F e) p = (inner ℝ n e) • secondFundamental F n p := by
  ext i j
  rw [covHessian_height_eq_residual g hF.1 hU hp,
    normalResidual_eq_secondFundamental_smul hg hF hU hp hn,
    real_inner_smul_left]
  change secondFundamental F n p i j * inner ℝ n e =
    inner ℝ n e * secondFundamental F n p i j
  exact mul_comm _ _

end SmoothLocal.Geometry

end

end OAI
