import OAI.Geometry.EinsteinFour.WeylNormal
import OAI.Geometry.EinsteinFour.FrameCurvature

namespace OAI

/-! The normal Jacobi trace follows from the classical Einstein curvature
decomposition and the two trace-free Weyl blocks. -/

namespace PositiveEinsteinFour.Angular

open Matrix

theorem rotated_trace (U : Mat3) (q : Directions) : (rotated U q).trace = U.trace := by
  have hO : (mixingMatrix q)ᵀ * mixingMatrix q = 1 :=
    mul_eq_one_comm.mp (mixing_orthogonal q)
  rw [rotated, Matrix.trace_mul_cycle, hO, one_mul]

theorem normalDeviation_trace (T U : Mat3) (q : Directions)
    (hT : T.trace = 0) (hU : U.trace = 0) :
    (normalDeviation T U q).trace = 0 := by
  simp [normalDeviation, Matrix.trace_smul, Matrix.trace_add, rotated_trace, hT, hU]

end PositiveEinsteinFour.Angular

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular
open scoped Manifold ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem normalCurvature_trace (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (q : Directions)
    (hdec : frameCurvature g c e = einsteinCurvatureTensor (plusWeyl g c e)
      (minusWeyl g c e))
    (hT : (plusWeyl g c e).trace = 0) (hU : (minusWeyl g c e).trace = 0) :
    (normalCurvature g c e q).trace = 3 := by
  rw [normalCurvature_eq_of_decomposition g c e hdec q, Matrix.trace_add,
    normalDeviation_trace _ _ _ hT hU]
  norm_num [Matrix.trace_one]

theorem frameCurvatureField_add_one_trace (g : SmoothMetric M) (e : FrameBundle g)
    (hdec : frameCurvature g e.base e.frame =
      einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (hT : (plusWeyl g e.base e.frame).trace = 0)
    (hU : (minusWeyl g e.base e.frame).trace = 0) :
    ((1 : Mat3) + frameCurvatureField g e).trace = 3 := by
  have he : (1 : Mat3) + (normalCurvature g e.base e.frame firstDirection - 1) =
      normalCurvature g e.base e.frame firstDirection := by abel
  change ((1 : Mat3) + (normalCurvature g e.base e.frame firstDirection - 1)).trace = 3
  rw [he]
  exact normalCurvature_trace g e.base e.frame firstDirection hdec hT hU

end PositiveEinsteinFour.Geometry

end OAI
