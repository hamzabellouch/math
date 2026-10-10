import OAI.Geometry.EinsteinFour.FrameBundle
import OAI.Geometry.EinsteinFour.AngularCurvature

namespace OAI

/-! Complete each unit direction to its quaternionic orthonormal frame.
This relates spherical fiber averages to actual orthonormal frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular
open scoped Manifold ContDiff

noncomputable section

def directionFrameMatrix (q : Directions) : Mat4 :=
  ![![q.val 0, -q.val 1, -q.val 2, -q.val 3],
    ![q.val 1, q.val 0, q.val 3, -q.val 2],
    ![q.val 2, -q.val 3, q.val 0, q.val 1],
    ![q.val 3, q.val 2, -q.val 1, q.val 0]]

theorem directionFrameMatrix_zero (q : Directions) (i : Fin 4) :
    directionFrameMatrix q i 0 = q.val i := by
  fin_cases i <;> rfl

theorem directionFrameMatrix_succ (q : Directions) (i : Fin 4) (s : Fin 3) :
    directionFrameMatrix q i s.succ = normalVector q s i := by
  fin_cases i <;> fin_cases s <;>
    simp [directionFrameMatrix, normalVector, TraceHessian.quaternionMatrix,
      Fin.sum_univ_succ]

theorem directionFrameMatrix_orthogonal (q : Directions) :
    (directionFrameMatrix q)ᵀ * directionFrameMatrix q = 1 := by
  ext i j
  change (∑ k, directionFrameMatrix q k i * directionFrameMatrix q k j) =
    if i = j then 1 else 0
  calc
    _ = (∑ k, q.val k ^ 2) * (if i = j then 1 else 0) := by
      fin_cases i <;> fin_cases j <;>
        simp [directionFrameMatrix, Fin.sum_univ_succ]
      all_goals ring
    _ = _ := by rw [direction_sum_sq]; simp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def OrthonormalFrame.turn {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (q : Directions) : OrthonormalFrame g c where
  matrix := e.matrix * directionFrameMatrix q
  orthonormal := by
    calc
      (e.matrix * directionFrameMatrix q)ᵀ * chartMetric g c *
          (e.matrix * directionFrameMatrix q) =
          (directionFrameMatrix q)ᵀ *
            (e.matrixᵀ * chartMetric g c * e.matrix) * directionFrameMatrix q := by
        rw [Matrix.transpose_mul]
        noncomm_ring
      _ = 1 := by rw [e.orthonormal, mul_one, directionFrameMatrix_orthogonal]

theorem OrthonormalFrame.turn_first {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (q : Directions) :
    (e.turn q).vector 0 = e.map q.val := by
  ext i
  change (∑ j, e.matrix i j * directionFrameMatrix q j 0) =
    ∑ j, e.matrix i j * q.val j
  simp only [directionFrameMatrix_zero]

def frameTurn {g : SmoothMetric M} {c : M} (e : OrthonormalFrame g c)
    (q : Directions) : FrameBundle g := ⟨c, e.turn q⟩

end

end PositiveEinsteinFour.Geometry

end OAI
