import OAI.Geometry.IsometricImmersion.Curvature.AffineConnection

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def ordinaryCoordinateHessian (z : Coord → ℝ) (p : Coord) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => coordPartial i (coordPartial j z) p

def connectionHessianCorrection (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  ∑ k, christoffel g k i j p * coordPartial k z p

theorem covHessian_eq_ordinary_sub_correction (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    covHessian g z p = ordinaryCoordinateHessian z p - connectionHessianCorrection g z p := rfl

theorem ordinaryCoordinateHessian_affine_comp {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hq : affineCoordinates b R q ∈ U) :
    ordinaryCoordinateHessian (z ∘ affineCoordinates b R) q =
      Rᵀ * ordinaryCoordinateHessian z (affineCoordinates b R q) * R := by
  have hB : ordinaryCoordinateHessian z (affineCoordinates b R q) =
      bilinearMatrix (fderiv ℝ (fderiv ℝ z) (affineCoordinates b R q)) := by
    ext i j
    exact second_coordPartial_eq_fderiv hz hU hq i j
  rw [hB]
  ext i j
  change coordPartial i (coordPartial j (z ∘ affineCoordinates b R)) q = _
  rw [second_coordPartial_affine_comp hz hU b R q hq i j]
  exact bilinear_matrix_congruence (fderiv ℝ (fderiv ℝ z) (affineCoordinates b R q)) R i j

theorem connectionHessianCorrection_affine_comp
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) :
    connectionHessianCorrection (affinePullbackMetric g b R) (z ∘ affineCoordinates b R) q =
      Rᵀ * connectionHessianCorrection g z (affineCoordinates b R q) * R := by
  have hdz : DifferentiableAt ℝ z (affineCoordinates b R q) :=
    (((hz _ hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))
  have hchain (k : Fin 2) : coordPartial k (z ∘ affineCoordinates b R) q =
      ∑ a, R a k * coordPartial a z (affineCoordinates b R q) :=
    coordPartial_affine_comp b R q hdz k
  ext i j
  change (∑ k, christoffel (affinePullbackMetric g b R) k i j q *
    coordPartial k (z ∘ affineCoordinates b R) q) = _
  simp only [hchain]
  calc
    _ = ∑ a, coordPartial a z (affineCoordinates b R q) *
        (∑ k, R a k * christoffel (affinePullbackMetric g b R) k i j q) := by
      simp only [Fin.sum_univ_two]
      ring
    _ = ∑ a, coordPartial a z (affineCoordinates b R q) *
        (∑ c, ∑ d, R c i * R d j * christoffel g a c d (affineCoordinates b R q)) := by
      simp_rw [christoffel_affinePullback_push hg hU b R hR q hq]
    _ = _ := by
      simp only [connectionHessianCorrection, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_two]
      ring

theorem covHessian_affinePullback
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) :
    covHessian (affinePullbackMetric g b R) (z ∘ affineCoordinates b R) q =
      Rᵀ * covHessian g z (affineCoordinates b R q) * R := by
  rw [covHessian_eq_ordinary_sub_correction, covHessian_eq_ordinary_sub_correction,
    ordinaryCoordinateHessian_affine_comp hz hU b R q hq,
    connectionHessianCorrection_affine_comp hg hz hU b R hR q hq]
  simp only [Matrix.mul_sub, Matrix.sub_mul]

def coordinateCovector (z : Coord → ℝ) (p : Coord) : Coord := fun i => coordPartial i z p

theorem coordinateCovector_affine_comp {z : Coord → ℝ}
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hz : DifferentiableAt ℝ z (affineCoordinates b R q)) :
    coordinateCovector (z ∘ affineCoordinates b R) q =
      Rᵀ *ᵥ coordinateCovector z (affineCoordinates b R q) := by
  ext i
  exact coordPartial_affine_comp b R q hz i

theorem covectorNormSq_eq_dotProduct (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    covectorNormSq g z p = coordinateCovector z p ⬝ᵥ
      (inverseMetric g p *ᵥ coordinateCovector z p) := by
  simp only [covectorNormSq, coordinateCovector, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem inverseMetric_affinePullback (g : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord) :
    inverseMetric (affinePullbackMetric g b R) q =
      R⁻¹ * inverseMetric g (affineCoordinates b R q) * R⁻¹ᵀ := by
  simp only [inverseMetric, affinePullbackMetric, Matrix.mul_inv_rev,
    ← Matrix.transpose_nonsing_inv, Matrix.mul_assoc]

theorem covectorNormSq_affinePullback {g : MetricField} {z : Coord → ℝ}
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hz : DifferentiableAt ℝ z (affineCoordinates b R q)) :
    covectorNormSq (affinePullbackMetric g b R) (z ∘ affineCoordinates b R) q =
      covectorNormSq g z (affineCoordinates b R q) := by
  have hRS := Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det _).mp hR)
  have hT : R⁻¹ᵀ * Rᵀ = 1 := by rw [← Matrix.transpose_mul, hRS, Matrix.transpose_one]
  let v := coordinateCovector z (affineCoordinates b R q)
  have hvec : R⁻¹ᵀ *ᵥ (Rᵀ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
  have hquad := matrix_pullback_bilinear (inverseMetric g (affineCoordinates b R q))
    R⁻¹ᵀ (Rᵀ *ᵥ v) (Rᵀ *ᵥ v)
  simp only [hvec, Matrix.transpose_transpose] at hquad
  rw [covectorNormSq_eq_dotProduct, covectorNormSq_eq_dotProduct,
    coordinateCovector_affine_comp b R q hz, inverseMetric_affinePullback]
  exact hquad.symm

theorem heightEnergy_affinePullback {g : MetricField} {z : Coord → ℝ}
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hz : DifferentiableAt ℝ z (affineCoordinates b R q)) :
    heightEnergy (affinePullbackMetric g b R) (z ∘ affineCoordinates b R) q =
      R.det ^ 2 * heightEnergy g z (affineCoordinates b R q) := by
  rw [heightEnergy, covectorNormSq_affinePullback b R hR q hz]
  simp only [affinePullbackMetric, Matrix.det_mul, Matrix.det_transpose, heightEnergy]
  ring

theorem heightEnergy_affinePullback_pos_iff {g : MetricField} {z : Coord → ℝ}
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hz : DifferentiableAt ℝ z (affineCoordinates b R q)) :
    0 < heightEnergy (affinePullbackMetric g b R) (z ∘ affineCoordinates b R) q ↔
      0 < heightEnergy g z (affineCoordinates b R q) := by
  rw [heightEnergy_affinePullback b R hR q hz]
  exact mul_pos_iff_of_pos_left (sq_pos_of_ne_zero ((Matrix.isUnit_iff_isUnit_det _).mp hR).ne_zero)

end SmoothLocal.Geometry

end

end OAI
