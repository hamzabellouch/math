import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarDerivativeBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarPeriodicProperties
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-! Conversion of the processor's derivative bounds to the Euclidean norms
used in the velocity detector. The factor two is deliberately integral and
is computed from the two-dimensional norm comparison. -/

noncomputable section
namespace ForcedComputation
open ShearFlows
open scoped NNReal

abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

def planeCoordinates : EuclideanPlane ≃L[ℝ] Plane :=
  letI := ShearFlows.twoAtLeastTwo
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)

theorem planeCoordinates_norm_le (x : EuclideanPlane) :
    ‖planeCoordinates x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  exact PiLp.norm_apply_le x i

theorem planeCoordinates_symm_norm_le (x : Plane) :
    ‖planeCoordinates.symm x‖ ≤ 2 * ‖x‖ := by
  have h0 := norm_le_pi_norm x 0
  have h1 := norm_le_pi_norm x 1
  have h0sq := pow_le_pow_left₀ (norm_nonneg (x 0)) h0 2
  have h1sq := pow_le_pow_left₀ (norm_nonneg (x 1)) h1 2
  have hs := EuclideanSpace.norm_sq_eq (planeCoordinates.symm x)
  simp only [Fin.sum_univ_two, planeCoordinates,
    PiLp.coe_symm_continuousLinearEquiv, PiLp.toLp_apply] at hs
  change ‖WithLp.toLp 2 x‖ ≤ 2 * ‖x‖
  nlinarith [norm_nonneg x, norm_nonneg (WithLp.toLp 2 x),
    norm_nonneg (x 0), norm_nonneg (x 1)]

def euclideanMap (f : Plane → Plane) : EuclideanPlane → EuclideanPlane :=
  fun x => planeCoordinates.symm (f (planeCoordinates x))

def euclideanLinear (A : Plane →L[ℝ] Plane) : EuclideanPlane →L[ℝ] EuclideanPlane :=
  planeCoordinates.symm.toContinuousLinearMap.comp
    (A.comp planeCoordinates.toContinuousLinearMap)

theorem euclideanLinear_norm_le (A : Plane →L[ℝ] Plane) :
    ‖euclideanLinear A‖ ≤ 2 * ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  calc
    ‖euclideanLinear A x‖ ≤ 2 * ‖A (planeCoordinates x)‖ :=
      planeCoordinates_symm_norm_le _
    _ ≤ 2 * (‖A‖ * ‖planeCoordinates x‖) := by
      gcongr
      exact A.le_opNorm _
    _ ≤ 2 * (‖A‖ * ‖x‖) := by
      gcongr
      exact planeCoordinates_norm_le x
    _ = _ := by ring

theorem euclideanMap_fderiv {f : Plane → Plane} {x : EuclideanPlane}
    (hf : DifferentiableAt ℝ f (planeCoordinates x)) :
    fderiv ℝ (euclideanMap f) x = euclideanLinear (fderiv ℝ f (planeCoordinates x)) := by
  exact (planeCoordinates.symm.toContinuousLinearMap.hasFDerivAt.comp x
    (hf.hasFDerivAt.comp x planeCoordinates.toContinuousLinearMap.hasFDerivAt)).fderiv

theorem euclideanLinear_sub (A B : Plane →L[ℝ] Plane) :
    euclideanLinear (A - B) = euclideanLinear A - euclideanLinear B := by
  ext x
  simp [euclideanLinear]

theorem euclideanLinear_lipschitz : LipschitzWith 2 euclideanLinear := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simpa only [dist_eq_norm, ← euclideanLinear_sub, NNReal.coe_ofNat] using
    euclideanLinear_norm_le (A - B)

theorem planeCoordinates_lipschitz : LipschitzWith 1 planeCoordinates := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul] using
    planeCoordinates_norm_le (x - y)

theorem euclideanMap_second_bound {f : Plane → Plane} {K : ℝ≥0}
    (hf : Differentiable ℝ f) (hK : LipschitzWith K (fderiv ℝ f))
    (x : EuclideanPlane) :
    ‖fderiv ℝ (fderiv ℝ (euclideanMap f)) x‖ ≤ 2 * (K : ℝ) := by
  have he : fderiv ℝ (euclideanMap f) =
      fun y => euclideanLinear (fderiv ℝ f (planeCoordinates y)) :=
    funext fun y => euclideanMap_fderiv (hf _)
  rw [he]
  have h := euclideanLinear_lipschitz.comp (hK.comp planeCoordinates_lipschitz)
  simpa only [Function.comp_def, mul_one, NNReal.coe_mul, NNReal.coe_ofNat] using
    norm_fderiv_le_of_lipschitz ℝ h

def euclideanVariationCoefficient (H : FieldExpr) : ℕ :=
  2 * planarVariationCoefficient H

theorem planar_euclidean_derivative_bounds {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) (s : ℝ) (x : EuclideanPlane) :
    ‖fderiv ℝ (euclideanMap (planarSlice H s)) x‖ ≤
        (euclideanVariationCoefficient H : ℝ) ∧
      ‖fderiv ℝ (fderiv ℝ (euclideanMap (planarSlice H s))) x‖ ≤
        (euclideanVariationCoefficient H : ℝ) := by
  have hf := (planarSlice_smooth hH s).differentiable (by simp)
  constructor
  · rw [euclideanMap_fderiv (hf _)]
    apply (euclideanLinear_norm_le _).trans
    have hb := (planar_derivative_bounds hH hT s (planeCoordinates x)).1
    simp only [euclideanVariationCoefficient, Nat.cast_mul, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  · have hb := euclideanMap_second_bound hf (planarSlice_fderiv_lipschitz hH hT s) x
    simp only [euclideanVariationCoefficient, planarVariationCoefficient,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, NNReal.coe_natCast] at *
    have hk : (0 : ℝ) ≤ suspensionLipschitzBound H := Nat.cast_nonneg _
    linarith

end ForcedComputation

end

end OAI
