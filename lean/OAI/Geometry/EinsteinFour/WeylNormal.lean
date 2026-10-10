import OAI.Geometry.EinsteinFour.AngularCurvature
import OAI.Geometry.EinsteinFour.AngularDerivativeMoments
import OAI.Geometry.EinsteinFour.WeylDerivative
import Mathlib.Analysis.Matrix.Normed

namespace OAI

/-! Link the normal-tensor calculation to the concrete metric. The classical
curvature decomposition is displayed as an explicit local hypothesis here;
the angular mean identities themselves are proved, not postulated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

local instance : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup

theorem squareNorm_eq_frobenius_norm_sq (T : Mat3) : squareNorm T = ‖T‖ ^ 2 := by
  symm
  simp only [Matrix.frobenius_norm_def, Real.rpow_two, ← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt (by positivity)]
  simp only [squareNorm, Real.norm_eq_abs, sq_abs]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def normalCurvature (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (q : Directions) : Mat3 := fun i j =>
  normalEvaluation q i j (frameCurvature g c e)

def normalCurvatureDeviation (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (q : Directions) : Mat3 :=
  normalCurvature g c e q - 1

theorem normalCurvature_eq_of_decomposition
    (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (hdecomp : frameCurvature g c e =
      einsteinCurvatureTensor (plusWeyl g c e) (minusWeyl g c e)) (q : Directions) :
    normalCurvature g c e q = 1 + normalDeviation (plusWeyl g c e) (minusWeyl g c e) q := by
  ext i j
  change normalEvaluation q i j (frameCurvature g c e) = _
  rw [hdecomp]
  exact normalEvaluation_einstein (plusWeyl g c e) (minusWeyl g c e) q i j

theorem normalCurvatureDeviation_eq_of_decomposition
    (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (hdecomp : frameCurvature g c e =
      einsteinCurvatureTensor (plusWeyl g c e) (minusWeyl g c e)) (q : Directions) :
    normalCurvatureDeviation g c e q =
      normalDeviation (plusWeyl g c e) (minusWeyl g c e) q := by
  rw [normalCurvatureDeviation, normalCurvature_eq_of_decomposition g c e hdecomp]
  abel

theorem normalCurvatureDeviation_mean_square
    (h : FollandMoments) (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (hdecomp : frameCurvature g c e =
      einsteinCurvatureTensor (plusWeyl g c e) (minusWeyl g c e))
    (hT : (plusWeyl g c e).trace = 0) (hU : (minusWeyl g c e).trace = 0) :
    (∫ q, squareNorm (normalCurvatureDeviation g c e q) ∂sphereMeasure) =
      (3 / 2) * (normalizedBlockNorm (plusWeyl g c e) ^ 2 +
        normalizedBlockNorm (minusWeyl g c e) ^ 2) := by
  simp_rw [normalCurvatureDeviation_eq_of_decomposition g c e hdecomp]
  exact integral_squareNorm_normalDeviation_normalized h _ _ hT hU

/-- The derivative field uses the metric's actual covariant derivatives. -/
def normalCurvatureDerivative (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (q : Directions) : Mat3 :=
  normalDerivative (plusWeylGradient g c e) (minusWeylGradient g c e) q

theorem normalCurvatureDerivative_mean_square
    (h : FollandMoments) (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (hTs : ∀ a, (plusWeylGradient g c e a)ᵀ = plusWeylGradient g c e a)
    (hTt : ∀ a, (plusWeylGradient g c e a).trace = 0) :
    (∫ q, squareNorm (normalCurvatureDerivative g c e q) ∂sphereMeasure) =
      (gradientSquareNorm (plusWeylGradient g c e) +
        gradientSquareNorm (minusWeylGradient g c e)) / 16 := by
  exact integral_normalDerivative_squareNorm_exact h _ _ hTs hTt

theorem normalCurvatureDeviation_mean_frobenius
    (h : FollandMoments) (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (hdecomp : frameCurvature g c e =
      einsteinCurvatureTensor (plusWeyl g c e) (minusWeyl g c e))
    (hT : (plusWeyl g c e).trace = 0) (hU : (minusWeyl g c e).trace = 0) :
    (∫ q, ‖normalCurvatureDeviation g c e q‖ ^ 2 ∂sphereMeasure) =
      (3 / 2) * (normalizedBlockNorm (plusWeyl g c e) ^ 2 +
        normalizedBlockNorm (minusWeyl g c e) ^ 2) := by
  simpa only [squareNorm_eq_frobenius_norm_sq] using
    normalCurvatureDeviation_mean_square h g c e hdecomp hT hU

end

end PositiveEinsteinFour.Geometry

end OAI
