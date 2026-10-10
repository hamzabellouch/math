import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarPerturbations
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.SecondDerivativeBounds

namespace OAI

/-! Uniform, explicitly computed bounds for both spatial derivatives of the
planar field. The extra coordinate in the autonomous suspension does not
increase the norm when a planar displacement is included. -/

noncomputable section
namespace ForcedComputation
open ShearFlows
open scoped NNReal

def horizontalLinear : Space →L[ℝ] Plane :=
  ContinuousLinearMap.pi (fun j : Fin 2 => ContinuousLinearMap.proj j.castSucc)

def planeSpaceTimeInclusion : Plane →L[ℝ] SpaceTime :=
  (0 : Plane →L[ℝ] ℝ).prod planeInclusion

theorem planeSpaceTimeInclusion_norm (v : Plane) :
    ‖planeSpaceTimeInclusion v‖ = ‖v‖ := by
  change ‖((0 : ℝ), atHeight v 0)‖ = ‖v‖
  simp only [Prod.norm_def, norm_zero, atHeight_zero_norm, max_eq_right (norm_nonneg v)]

theorem planarSlice_fderiv {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) (s : ℝ) (x : Plane) :
    fderiv ℝ (planarSlice H s) x = horizontalLinear.comp
      ((fderiv ℝ (SpatialExpression.suspensionCode H).val (0, atHeight x s)).comp
        planeSpaceTimeInclusion) := by
  have he : planarSlice H s = fun Y =>
      horizontalLinear ((SpatialExpression.suspensionCode H).val (0, atHeight Y s)) := by
    funext Y
    rw [SpatialExpression.suspensionCode_val hH hT, planarSlice_eq_horizontal hH]
    funext j
    fin_cases j <;> rfl
  have hi : HasFDerivAt (fun Y : Plane => ((0 : ℝ), atHeight Y s))
      planeSpaceTimeInclusion x :=
    (hasFDerivAt_const (0 : ℝ) x).prodMk (atHeight_hasFDerivAt x s)
  have hv := ((VelocityExpr.smooth (SpatialExpression.suspensionCode_valid hH)).differentiable
    (by simp) (0, atHeight x s)).hasFDerivAt.comp x hi
  rw [he]
  exact (horizontalLinear.hasFDerivAt.comp x hv).fderiv

def planarSecondBound (H : FieldExpr) : ℕ :=
  (SpatialExpression.suspensionCode H).secondModulusBound

theorem planarSlice_fderiv_lipschitz {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) (s : ℝ) :
    LipschitzWith (planarSecondBound H : ℝ≥0) (fderiv ℝ (planarSlice H s)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, planarSlice_fderiv hH hT, planarSlice_fderiv hH hT]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  let A := fderiv ℝ (SpatialExpression.suspensionCode H).val (0, atHeight x s) -
    fderiv ℝ (SpatialExpression.suspensionCode H).val (0, atHeight y s)
  change ‖horizontal (A (planeSpaceTimeInclusion v))‖ ≤ _
  have hb := VelocityExpr.fderiv_lipschitz_bound
    (SpatialExpression.suspensionCode_valid hH) (0, atHeight x s) (0, atHeight y s)
  have hd : ‖((0 : ℝ), atHeight x s) - (0, atHeight y s)‖ = dist x y := by
    rw [← dist_eq_norm, Prod.dist_eq, dist_self, atHeight_dist_same,
      max_eq_right dist_nonneg]
  calc
    ‖horizontal (A (planeSpaceTimeInclusion v))‖ ≤ ‖A (planeSpaceTimeInclusion v)‖ :=
      horizontal_norm_le _
    _ ≤ ‖A‖ * ‖planeSpaceTimeInclusion v‖ := A.le_opNorm _
    _ ≤ ((planarSecondBound H : ℝ) * dist x y) * ‖v‖ := by
      rw [planeSpaceTimeInclusion_norm]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
      simpa only [A, planarSecondBound, hd] using hb
    _ = _ := rfl

theorem planarSlice_second_fderiv_bound {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) (s : ℝ) (x : Plane) :
    ‖fderiv ℝ (fderiv ℝ (planarSlice H s)) x‖ ≤ (planarSecondBound H : ℝ) :=
  norm_fderiv_le_of_lipschitz ℝ (planarSlice_fderiv_lipschitz hH hT s)

def planarVariationCoefficient (H : FieldExpr) : ℕ :=
  1 + suspensionLipschitzBound H + planarSecondBound H

theorem planarVariationCoefficient_pos (H : FieldExpr) :
    0 < planarVariationCoefficient H := by
  unfold planarVariationCoefficient
  omega

theorem planar_derivative_bounds {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) (s : ℝ) (x : Plane) :
    ‖fderiv ℝ (planarSlice H s) x‖ ≤ (planarVariationCoefficient H : ℝ) ∧
      ‖fderiv ℝ (fderiv ℝ (planarSlice H s)) x‖ ≤
        (planarVariationCoefficient H : ℝ) := by
  have h₁ := planarSlice_fderiv_bound hH hT s x
  have h₂ := planarSlice_second_fderiv_bound hH hT s x
  have hk : (0 : ℝ) ≤ suspensionLipschitzBound H := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ planarSecondBound H := Nat.cast_nonneg _
  simp only [planarVariationCoefficient, Nat.cast_add, Nat.cast_one]
  constructor <;> linarith

end ForcedComputation

end

end OAI
