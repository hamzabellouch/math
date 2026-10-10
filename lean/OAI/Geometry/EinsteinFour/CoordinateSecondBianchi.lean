import OAI.Geometry.EinsteinFour.CurvatureSecondBianchi
import OAI.Geometry.EinsteinFour.CurvatureMetricSkew

namespace OAI

/-! Specialization of the second Bianchi algebra to the actual smooth
Christoffel symbols, with all four curvature slots differentiated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

private theorem matrixPartial_sub (A B : FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ j k, DifferentiableAt ℝ (fun w => A w j k) z)
    (hB : ∀ j k, DifferentiableAt ℝ (fun w => B w j k) z) (i : Fin 4) :
    matrixPartial (fun w => A w - B w) i z = matrixPartial A i z - matrixPartial B i z := by
  ext j k
  exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i))
    (fderiv_fun_sub (hA j k) (hB j k))

private theorem product_entries_differentiable (A B : FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ j k, DifferentiableAt ℝ (fun w => A w j k) z)
    (hB : ∀ j k, DifferentiableAt ℝ (fun w => B w j k) z) :
    ∀ j k, DifferentiableAt ℝ (fun w => (A w * B w) j k) z := by
  intro j k
  change DifferentiableAt ℝ (fun w => ∑ p, A w j p * B w p k) z
  exact DifferentiableAt.fun_sum (fun p _ => (hA j p).mul (hB p k))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem connectionMatrix_partial_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j a b : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => matrixPartial (connectionMatrix g c j) i w a b) z := by
  exact ((christoffel_contDiffAt g c z hz hdet a j b).fderiv_right
    (m := ∞) (by simp)).clm_apply contDiffAt_const

theorem coordinateCurvatureMatrix_eq_algebra (g : SmoothMetric M) (c : M)
    (z : FourSpace) (i j : Fin 4) :
    coordinateCurvatureMatrix g c i j z = CovariantBianchi.curvature
      (fun r => connectionMatrix g c r z)
      (fun r s => matrixPartial (connectionMatrix g c s) r z) i j := rfl

theorem coordinateCurvatureMatrix_contDiffAt (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j a b : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => coordinateCurvatureMatrix g c i j w a b) z := by
  have hp (r s : Fin 4) :
      ContDiffAt ℝ ∞ (fun w => (connectionMatrix g c r w *
        connectionMatrix g c s w) a b) z := by
    change ContDiffAt ℝ ∞ (fun w => ∑ p,
      christoffel g c w a r p * christoffel g c w p s b) z
    apply ContDiffAt.sum
    intro p _
    exact (christoffel_contDiffAt g c z hz hdet a r p).mul
      (christoffel_contDiffAt g c z hz hdet p s b)
  exact (((connectionMatrix_partial_contDiffAt g c z hz hdet i j a b).sub
    (connectionMatrix_partial_contDiffAt g c z hz hdet j i a b)).add (hp i j)).sub (hp j i)

theorem matrixPartial_coordinateCurvature (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j k : Fin 4) :
    matrixPartial (coordinateCurvatureMatrix g c j k) i z =
      CovariantBianchi.curvatureDerivative
        (fun r => connectionMatrix g c r z)
        (fun r s => matrixPartial (connectionMatrix g c s) r z)
        (fun r s t => matrixPartial (matrixPartial (connectionMatrix g c t) s) r z)
        i j k := by
  let A := connectionMatrix g c j
  let B := connectionMatrix g c k
  let F := matrixPartial B j
  let H := matrixPartial A k
  have hA : ∀ a b, DifferentiableAt ℝ (fun w => A w a b) z := fun a b =>
    (christoffel_contDiffAt g c z hz hdet a j b).differentiableAt (by simp)
  have hB : ∀ a b, DifferentiableAt ℝ (fun w => B w a b) z := fun a b =>
    (christoffel_contDiffAt g c z hz hdet a k b).differentiableAt (by simp)
  have hF : ∀ a b, DifferentiableAt ℝ (fun w => F w a b) z := fun a b =>
    (connectionMatrix_partial_contDiffAt g c z hz hdet j k a b).differentiableAt (by simp)
  have hH : ∀ a b, DifferentiableAt ℝ (fun w => H w a b) z := fun a b =>
    (connectionMatrix_partial_contDiffAt g c z hz hdet k j a b).differentiableAt (by simp)
  have hFH : ∀ a b, DifferentiableAt ℝ (fun w => (F w - H w) a b) z :=
    fun a b => (hF a b).sub (hH a b)
  have hAB := product_entries_differentiable A B z hA hB
  have hBA := product_entries_differentiable B A z hB hA
  have hsum : ∀ a b,
      DifferentiableAt ℝ (fun w => ((F w - H w) + A w * B w) a b) z :=
    fun a b => (hFH a b).add (hAB a b)
  change matrixPartial (fun w => (F w - H w) + A w * B w - B w * A w) i z = _
  rw [matrixPartial_sub _ _ z hsum hBA i,
    matrixPartial_add _ _ z hFH hAB i, matrixPartial_sub F H z hF hH i,
    matrixPartial_mul A B z hA hB i, matrixPartial_mul B A z hB hA i]
  dsimp only [A, B, F, H, CovariantBianchi.curvatureDerivative]
  abel

def coordinateCovariantCurvatureDerivative (g : SmoothMetric M) (c : M)
    (z : FourSpace) (i j k : Fin 4) : Mat4 :=
  matrixPartial (coordinateCurvatureMatrix g c j k) i z +
    connectionMatrix g c i z * coordinateCurvatureMatrix g c j k z -
    coordinateCurvatureMatrix g c j k z * connectionMatrix g c i z -
    ∑ p, (connectionMatrix g c i z p j • coordinateCurvatureMatrix g c p k z +
      connectionMatrix g c i z p k • coordinateCurvatureMatrix g c j p z)

theorem coordinateCovariantCurvatureDerivative_eq_algebra
    (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j k : Fin 4) :
    coordinateCovariantCurvatureDerivative g c z i j k =
      CovariantBianchi.tensorCurvatureDerivative
        (fun r => connectionMatrix g c r z)
        (fun r s => matrixPartial (connectionMatrix g c s) r z)
        (fun r s t => matrixPartial (matrixPartial (connectionMatrix g c t) s) r z)
        i j k := by
  unfold coordinateCovariantCurvatureDerivative
  rw [matrixPartial_coordinateCurvature g c z hz hdet]
  simp only [coordinateCurvatureMatrix_eq_algebra]
  rfl

theorem coordinate_second_bianchi (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j k : Fin 4) :
    coordinateCovariantCurvatureDerivative g c z i j k +
      coordinateCovariantCurvatureDerivative g c z j k i +
      coordinateCovariantCurvatureDerivative g c z k i j = 0 := by
  simp only [coordinateCovariantCurvatureDerivative_eq_algebra g c z hz hdet]
  apply CovariantBianchi.tensorCurvatureDerivative_cyclic
  · intro r s p
    exact christoffel_comm g c z p r s
  · intro r s t
    exact matrixPartial_comm (connectionMatrix g c t) z
      (fun a b => christoffel_contDiffAt g c z hz hdet a t b) r s

theorem coordinate_second_bianchi_at_center (g : SmoothMetric M) (c : M) (i j k : Fin 4) :
    coordinateCovariantCurvatureDerivative g c (chartAt FourSpace c c) i j k +
      coordinateCovariantCurvatureDerivative g c (chartAt FourSpace c c) j k i +
      coordinateCovariantCurvatureDerivative g c (chartAt FourSpace c c) k i j = 0 := by
  apply coordinate_second_bianchi
  · exact (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  · exact (chartMetric_posDef g c).det_pos.ne'

end
end PositiveEinsteinFour.Geometry

end OAI
