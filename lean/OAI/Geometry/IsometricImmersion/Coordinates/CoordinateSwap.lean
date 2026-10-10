import OAI.Geometry.IsometricImmersion.Curvature.AffineCurvature
import OAI.Geometry.IsometricImmersion.Calculus.AffineCovariantHessian

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def swapCoordinateIndex (i : Fin 2) : Fin 2 := ![1, 0] i

def coordinateSwapMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

def coordinateSwap : Coord → Coord := affineCoordinates 0 coordinateSwapMatrix

def swappedMetric (g : MetricField) : MetricField :=
  affinePullbackMetric g 0 coordinateSwapMatrix

def swappedHeight (z : Coord → ℝ) : Coord → ℝ := z ∘ coordinateSwap

@[simp] theorem swapCoordinateIndex_zero : swapCoordinateIndex 0 = 1 := rfl
@[simp] theorem swapCoordinateIndex_one : swapCoordinateIndex 1 = 0 := rfl

@[simp] theorem swapCoordinateIndex_involutive (i : Fin 2) :
    swapCoordinateIndex (swapCoordinateIndex i) = i := by
  fin_cases i <;> rfl

@[simp] theorem coordinateSwap_apply (p : Coord) (i : Fin 2) :
    coordinateSwap p i = p (swapCoordinateIndex i) := by
  fin_cases i <;>
    simp [coordinateSwap, affineCoordinates, coordinateSwapMatrix,
      dotProduct, Fin.sum_univ_two, swapCoordinateIndex]

@[simp] theorem coordinateSwap_involutive (p : Coord) :
    coordinateSwap (coordinateSwap p) = p := by
  ext i
  simp

@[simp] theorem coordinateSwapMatrix_det : coordinateSwapMatrix.det = -1 := by
  norm_num [coordinateSwapMatrix, Matrix.det_fin_two]

theorem coordinateSwapMatrix_isUnit : IsUnit coordinateSwapMatrix := by
  rw [Matrix.isUnit_iff_isUnit_det, coordinateSwapMatrix_det]
  exact isUnit_neg_one

theorem coordinateSwap_contDiff : ContDiff ℝ ∞ coordinateSwap :=
  affineCoordinates_contDiff 0 coordinateSwapMatrix

theorem coordinateSwap_preimage_isOpen {U : Set Coord} (hU : IsOpen U) :
    IsOpen (coordinateSwap ⁻¹' U) :=
  hU.preimage coordinateSwap_contDiff.continuous

theorem swappedMetric_smoothPositive {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) :
    SmoothPositiveOn (swappedMetric g) (coordinateSwap ⁻¹' U) :=
  affinePullbackMetric_smoothPositive hg 0 coordinateSwapMatrix
    (Matrix.mulVec_injective_of_isUnit coordinateSwapMatrix_isUnit)

theorem swappedHeight_contDiffOn {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (swappedHeight z) (coordinateSwap ⁻¹' U) :=
  affine_comp_contDiffOn hz 0 coordinateSwapMatrix

@[simp] theorem swappedMetric_apply (g : MetricField) (p : Coord) (i j : Fin 2) :
    swappedMetric g p i j =
      g (coordinateSwap p) (swapCoordinateIndex i) (swapCoordinateIndex j) := by
  fin_cases i <;> fin_cases j <;>
    simp [swappedMetric, affinePullbackMetric, coordinateSwapMatrix,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      coordinateSwap, swapCoordinateIndex]

@[simp] theorem swappedMetric_det (g : MetricField) (p : Coord) :
    (swappedMetric g p).det = (g (coordinateSwap p)).det := by
  simp only [Matrix.det_fin_two, swappedMetric_apply,
    swapCoordinateIndex_zero, swapCoordinateIndex_one]
  ring

theorem gaussianCurvature_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) :
    gaussianCurvature (swappedMetric g) p = gaussianCurvature g (coordinateSwap p) :=
  gaussianCurvature_affinePullback hg hU 0 coordinateSwapMatrix
    coordinateSwapMatrix_isUnit p hp

theorem christoffel_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (k i j : Fin 2) :
    christoffel (swappedMetric g) k i j p =
      christoffel g (swapCoordinateIndex k) (swapCoordinateIndex i)
        (swapCoordinateIndex j) (coordinateSwap p) := by
  have h := christoffel_affinePullback_push hg hU 0 coordinateSwapMatrix
    coordinateSwapMatrix_isUnit p hp (swapCoordinateIndex k) i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simpa [coordinateSwapMatrix, swapCoordinateIndex, Fin.sum_univ_two,
      swappedMetric, coordinateSwap] using h

theorem coordPartial_swap_comp {z : Coord → ℝ} {p : Coord}
    (hz : DifferentiableAt ℝ z (coordinateSwap p)) (i : Fin 2) :
    coordPartial i (swappedHeight z) p =
      coordPartial (swapCoordinateIndex i) z (coordinateSwap p) := by
  have h := coordPartial_affine_comp 0 coordinateSwapMatrix p hz i
  fin_cases i <;>
    simpa [coordinateSwapMatrix, swapCoordinateIndex, Fin.sum_univ_two,
      swappedHeight, coordinateSwap] using h

theorem second_coordPartial_swap_comp {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j (swappedHeight z)) p =
      coordPartial (swapCoordinateIndex i) (coordPartial (swapCoordinateIndex j) z)
        (coordinateSwap p) := by
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j)
    (ordinaryCoordinateHessian_affine_comp hz hU 0 coordinateSwapMatrix p hp)
  fin_cases i <;> fin_cases j <;>
    simpa [ordinaryCoordinateHessian, coordinateSwapMatrix, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two, swapCoordinateIndex,
      swappedHeight, coordinateSwap] using h

theorem covHessian_swappedMetric {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {p : Coord} (hp : coordinateSwap p ∈ U) (i j : Fin 2) :
    covHessian (swappedMetric g) (swappedHeight z) p i j =
      covHessian g z (coordinateSwap p) (swapCoordinateIndex i) (swapCoordinateIndex j) := by
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j)
    (covHessian_affinePullback hg hz hU 0 coordinateSwapMatrix
      coordinateSwapMatrix_isUnit p hp)
  fin_cases i <;> fin_cases j <;>
    simpa [coordinateSwapMatrix, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_two, swapCoordinateIndex, swappedMetric, swappedHeight,
      coordinateSwap] using h

theorem heightEnergy_swappedMetric {g : MetricField} {z : Coord → ℝ} {p : Coord}
    (hz : DifferentiableAt ℝ z (coordinateSwap p)) :
    heightEnergy (swappedMetric g) (swappedHeight z) p =
      heightEnergy g z (coordinateSwap p) := by
  simpa only [swappedMetric, swappedHeight, coordinateSwap,
    coordinateSwapMatrix_det, neg_one_sq, one_mul] using
    (heightEnergy_affinePullback (g := g) 0 coordinateSwapMatrix
      coordinateSwapMatrix_isUnit p hz)

end SmoothLocal.Geometry

end

end OAI
