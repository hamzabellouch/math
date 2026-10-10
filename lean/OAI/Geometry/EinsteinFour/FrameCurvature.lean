import OAI.Geometry.EinsteinFour.FrameRotation
import OAI.Geometry.EinsteinFour.WeylNormal

namespace OAI

/-! The two fields on the actual orthonormal frame bundle that enter the
geodesic mean-square argument. They are evaluations of the metric curvature
and its covariant derivative, with no independent curvature field. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular
open scoped Manifold ContDiff

noncomputable section

def firstDirection : Directions :=
  ⟨coordinateVector 0, by
    simp [coordinateVector]⟩

theorem firstDirection_apply (i : Fin 4) :
    firstDirection.val i = if i = 0 then 1 else 0 := by
  fin_cases i <;> rfl

theorem firstDirection_normal (i : Fin 3) (a : Fin 4) :
    normalVector firstDirection i a = if a = i.succ then 1 else 0 := by
  fin_cases i <;> fin_cases a <;>
    simp [normalVector, firstDirection, coordinateVector,
      TraceHessian.quaternionMatrix]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameCurvatureField (g : SmoothMetric M) (e : FrameBundle g) : Mat3 :=
  normalCurvatureDeviation g e.base e.frame firstDirection

def frameCurvatureDerivative (g : SmoothMetric M) (e : FrameBundle g) : Mat3 :=
  normalCurvatureDerivative g e.base e.frame firstDirection

theorem frameCurvatureField_apply (g : SmoothMetric M) (e : FrameBundle g)
    (i j : Fin 3) :
    frameCurvatureField g e i j =
      frameCurvature g e.base e.frame i.succ 0 0 j.succ - if i = j then 1 else 0 := by
  simp only [frameCurvatureField, normalCurvatureDeviation, normalCurvature,
    Matrix.sub_apply, Matrix.one_apply, normalEvaluation, firstDirection_normal,
    firstDirection_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

theorem frameCurvatureDerivative_eq (g : SmoothMetric M) (e : FrameBundle g) :
    frameCurvatureDerivative g e =
      normalDeviation (plusWeylGradient g e.base e.frame 0)
        (minusWeylGradient g e.base e.frame 0) firstDirection := by
  simp only [frameCurvatureDerivative, normalCurvatureDerivative, normalDerivative,
    directional, firstDirection_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end

end PositiveEinsteinFour.Geometry

end OAI
