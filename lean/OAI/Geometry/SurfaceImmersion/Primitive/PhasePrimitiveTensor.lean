import OAI.Geometry.SurfaceImmersion.Geometry.LocalizedTensorPullbackBound
import OAI.Geometry.Immersion.ClosedSurface.MetricCoordinates

namespace OAI

/-! The transported primitive is the square of the actual first phase
covector, with its supported amplitude. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.JetPolynomial

def firstPhaseCovector (T : Base → Base) (x : Base) : SmallModes.Base :=
  ((fderiv ℝ T x (coordinateVector 0)) 0,(fderiv ℝ T x (coordinateVector 1)) 0)

lemma tensorCoordinatePullback_first_square (T : Base → Base) (x : Base) (a : ℝ) :
    tensorCoordinatePullbackValue T x ![a^2,0,0] =
      a^2 • PhaseGeometry.covectorSquare (firstPhaseCovector T x) := by
  have hx : planeCoordinateIsometry.symm SmallModes.dx = coordinateVector 0 := by
    ext i
    fin_cases i <;> rfl
  have hy : planeCoordinateIsometry.symm SmallModes.dy = coordinateVector 1 := by
    ext i
    fin_cases i <;> rfl
  ext k
  rw [← tensorCoordinateJacobian_sum,Fin.sum_univ_three]
  fin_cases k <;> simp [tensorCoordinateJacobian,firstPhaseCovector,
    PhaseGeometry.covectorSquare,PhaseMean.firstDirection,PhaseMean.secondDirection,
    hx,hy] <;> ring

lemma localizedTensorPullback_first_square (T : Base → Base) (χ a : Base → ℝ) (x : Base) :
    localizedTensorPullback T χ (fun y => ![a y^2,0,0]) x =
      (χ x * (a (T x))^2) • PhaseGeometry.covectorSquare (firstPhaseCovector T x) := by
  rw [localizedTensorPullback,tensorCoordinatePullback_first_square,smul_smul]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
