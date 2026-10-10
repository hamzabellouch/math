import OAI.Geometry.EinsteinFour.ChartMetricSmoothness
import OAI.Geometry.EinsteinFour.CurvatureFirstBianchi

namespace OAI

/-! Differentiated metric compatibility gives skew-adjointness of actual
coordinate curvature, and hence the last-slot symmetry of frame curvature. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def matrixPartial (A : FourSpace → Mat4) (i : Fin 4) (z : FourSpace) : Mat4 :=
  fun j k => partialDeriv (fun w => A w j k) i z

def connectionMatrix (g : SmoothMetric M) (c : M) (i : Fin 4) (z : FourSpace) : Mat4 :=
  fun j k => christoffel g c z j i k

private theorem partial_mul {f h : FourSpace → ℝ} {z : FourSpace}
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) (i : Fin 4) :
    partialDeriv (fun w => f w * h w) i z =
      partialDeriv f i z * h z + f z * partialDeriv h i z := by
  simp only [partialDeriv, fderiv_fun_mul hf hh, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

theorem matrixPartial_add (A B : FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ j k, DifferentiableAt ℝ (fun w => A w j k) z)
    (hB : ∀ j k, DifferentiableAt ℝ (fun w => B w j k) z) (i : Fin 4) :
    matrixPartial (fun w => A w + B w) i z = matrixPartial A i z + matrixPartial B i z := by
  ext j k
  exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i))
    (fderiv_fun_add (hA j k) (hB j k))

theorem matrixPartial_mul (A B : FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ j k, DifferentiableAt ℝ (fun w => A w j k) z)
    (hB : ∀ j k, DifferentiableAt ℝ (fun w => B w j k) z) (i : Fin 4) :
    matrixPartial (fun w => A w * B w) i z =
      matrixPartial A i z * B z + A z * matrixPartial B i z := by
  ext j k
  change partialDeriv (fun w => ∑ p, A w j p * B w p k) i z = _
  unfold partialDeriv
  have hsum := fderiv_fun_sum (u := Finset.univ)
    (A := fun p w => A w j p * B w p k) (fun p _ => (hA j p).mul (hB p k))
  rw [hsum, _root_.sum_apply]
  change (∑ p, partialDeriv (fun w => A w j p * B w p k) i z) = _
  simp only [partial_mul (hA _ _) (hB _ _), Finset.sum_add_distrib,
    Matrix.add_apply, Matrix.mul_apply, matrixPartial]

theorem matrixPartial_transpose (A : FourSpace → Mat4) (i : Fin 4) (z : FourSpace) :
    matrixPartial (fun w => (A w)ᵀ) i z = (matrixPartial A i z)ᵀ := rfl

theorem matrixPartial_congr {A B : FourSpace → Mat4} {z : FourSpace}
    (h : A =ᶠ[𝓝 z] B) (i : Fin 4) : matrixPartial A i z = matrixPartial B i z := by
  ext j k
  have he : (fun w => A w j k) =ᶠ[𝓝 z] (fun w => B w j k) :=
    h.mono fun _ hw => congrFun (congrFun hw j) k
  exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) he.fderiv_eq

theorem matrixPartial_comm (A : FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ j k, ContDiffAt ℝ ∞ (fun w => A w j k) z) (i j : Fin 4) :
    matrixPartial (matrixPartial A j) i z = matrixPartial (matrixPartial A i) j z := by
  ext k l
  have hd := ((hA k l).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have he (r s : Fin 4) :
      partialDeriv (fun w => partialDeriv (fun y => A y k l) s w) r z =
        fderiv ℝ (fderiv ℝ (fun y => A y k l)) z (coordinateVector r) (coordinateVector s) := by
    unfold partialDeriv
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  change partialDeriv (fun w => partialDeriv (fun y => A y k l) j w) i z =
    partialDeriv (fun w => partialDeriv (fun y => A y k l) i w) j z
  rw [he, he]
  exact ((hA k l).isSymmSndFDerivAt (by simp)).eq _ _

theorem matrixPartial_metric (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hG : IsUnit (metricInChart g c z).det) (i : Fin 4) :
    matrixPartial (metricInChart g c) i z =
      (connectionMatrix g c i z)ᵀ * metricInChart g c z +
        metricInChart g c z * connectionMatrix g c i z := by
  ext j k
  symm
  change (∑ p, christoffel g c z p i j * metricInChart g c z p k) +
      (∑ p, metricInChart g c z j p * christoffel g c z p i k) =
      partialDeriv (fun w => metricInChart g c w j k) i z
  rw [← Finset.sum_add_distrib]
  convert christoffel_metric_compatibility g c z hG i j k using 1
  apply Finset.sum_congr rfl
  intro p _
  rw [metricInChart_comm g c z p k]
  ring

private theorem matrix_mul_differentiable (A B : FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ j k, DifferentiableAt ℝ (fun w => A w j k) z)
    (hB : ∀ j k, DifferentiableAt ℝ (fun w => B w j k) z) :
    ∀ j k, DifferentiableAt ℝ (fun w => (A w * B w) j k) z := by
  intro j k
  change DifferentiableAt ℝ (fun w => ∑ p, A w j p * B w p k) z
  exact DifferentiableAt.fun_sum (fun p _ => (hA j p).mul (hB p k))

theorem matrixPartial_metric_second (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j : Fin 4) :
    matrixPartial (matrixPartial (metricInChart g c) j) i z =
      (matrixPartial (connectionMatrix g c j) i z)ᵀ * metricInChart g c z +
      (connectionMatrix g c j z)ᵀ * matrixPartial (metricInChart g c) i z +
      matrixPartial (metricInChart g c) i z * connectionMatrix g c j z +
      metricInChart g c z * matrixPartial (connectionMatrix g c j) i z := by
  let G := metricInChart g c
  let A := connectionMatrix g c j
  have hG : ∀ r t, DifferentiableAt ℝ (fun w => G w r t) z :=
    fun r t => (metricInChart_contDiffAt g c z hz r t).differentiableAt (by simp)
  have hA : ∀ r t, DifferentiableAt ℝ (fun w => A w r t) z :=
    fun r t => (christoffel_contDiffAt g c z hz hdet r j t).differentiableAt (by simp)
  have hAt : ∀ r t, DifferentiableAt ℝ (fun w => (A w)ᵀ r t) z := fun r t => hA t r
  have hGc : ContinuousAt G z := continuousAt_pi.mpr fun r =>
    continuousAt_pi.mpr fun t => (hG r t).continuousAt
  have hdc : ContinuousAt (fun w => (G w).det) z :=
    (continuous_id.matrix_det).continuousAt.comp hGc
  have heq : matrixPartial G j =ᶠ[𝓝 z] (fun w => (A w)ᵀ * G w + G w * A w) := by
    filter_upwards [hdc.eventually_ne hdet] with w hw
    exact matrixPartial_metric g c w (isUnit_iff_ne_zero.mpr hw) j
  change matrixPartial (matrixPartial G j) i z = _
  rw [matrixPartial_congr heq i,
    matrixPartial_add _ _ z (matrix_mul_differentiable _ _ z hAt hG)
      (matrix_mul_differentiable _ _ z hG hA) i,
    matrixPartial_mul _ _ z hAt hG i, matrixPartial_mul _ _ z hG hA i,
    matrixPartial_transpose]
  change ((matrixPartial A i z)ᵀ * G z + (A z)ᵀ * matrixPartial G i z) +
      (matrixPartial G i z * A z + G z * matrixPartial A i z) = _
  dsimp only [A, G]
  abel

def coordinateCurvatureMatrix (g : SmoothMetric M) (c : M) (i j : Fin 4)
    (z : FourSpace) : Mat4 :=
  matrixPartial (connectionMatrix g c j) i z -
    matrixPartial (connectionMatrix g c i) j z +
    connectionMatrix g c i z * connectionMatrix g c j z -
    connectionMatrix g c j z * connectionMatrix g c i z

theorem coordinateCurvatureMatrix_apply (g : SmoothMetric M) (c : M)
    (i j : Fin 4) (z : FourSpace) (k l : Fin 4) :
    coordinateCurvatureMatrix g c i j z k l = curvatureComponent g c z k i j l := by
  simp only [coordinateCurvatureMatrix, matrixPartial, connectionMatrix, Matrix.sub_apply,
    Matrix.add_apply, Matrix.mul_apply, curvatureComponent, Finset.sum_sub_distrib]
  ring

theorem coordinateCurvatureMatrix_skew (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j : Fin 4) :
    (coordinateCurvatureMatrix g c i j z)ᵀ * metricInChart g c z +
      metricInChart g c z * coordinateCurvatureMatrix g c i j z = 0 := by
  apply curvature_matrix_skew_of_metric_differentials
  have hh := matrixPartial_comm (metricInChart g c) z
    (metricInChart_contDiffAt g c z hz) i j
  rw [matrixPartial_metric_second g c z hz hdet i j,
    matrixPartial_metric_second g c z hz hdet j i,
    matrixPartial_metric g c z (isUnit_iff_ne_zero.mpr hdet) i,
    matrixPartial_metric g c z (isUnit_iff_ne_zero.mpr hdet) j] at hh
  exact hh

theorem lowered_curvature_last_skew (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j k l : Fin 4) :
    (∑ a, metricInChart g c z a k * curvatureComponent g c z a i j l) =
      -(∑ a, metricInChart g c z a l * curvatureComponent g c z a i j k) := by
  have hh := congrFun (congrFun (coordinateCurvatureMatrix_skew g c z hz hdet i j) k) l
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    coordinateCurvatureMatrix_apply, Matrix.zero_apply] at hh
  have hleft : (∑ a, curvatureComponent g c z a i j k * metricInChart g c z a l) =
      ∑ a, metricInChart g c z a l * curvatureComponent g c z a i j k := by
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hright : (∑ a, metricInChart g c z k a * curvatureComponent g c z a i j l) =
      ∑ a, metricInChart g c z a k * curvatureComponent g c z a i j l := by
    apply Finset.sum_congr rfl
    intro a _
    rw [metricInChart_comm g c z k a]
  rw [hleft, hright] at hh
  linarith

theorem lowered_curvature_last_skew_at_center (g : SmoothMetric M) (c : M)
    (i j k l : Fin 4) :
    (∑ a, chartMetric g c a k * curvatureComponent g c (chartAt FourSpace c c) a i j l) =
      -(∑ a, chartMetric g c a l * curvatureComponent g c (chartAt FourSpace c c) a i j k) := by
  apply lowered_curvature_last_skew
  · exact (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  · exact (chartMetric_posDef g c).det_pos.ne'

end
end PositiveEinsteinFour.Geometry

end OAI
