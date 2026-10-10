import OAI.Geometry.Relativity.CKS.VolumeDefinitions

namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSIntrinsicVolume

abbrev stdBasis : Module.Basis (Fin 3) ℝ E := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

lemma sqrt_gram_det_comp (B : LinearMap.BilinForm ℝ E) (L : E →L[ℝ] E) :
    Real.sqrt (LinearMap.BilinForm.toMatrix stdBasis
      (B.comp L.toLinearMap L.toLinearMap)).det =
      |L.det| * Real.sqrt (LinearMap.BilinForm.toMatrix stdBasis B).det := by
  rw [LinearMap.BilinForm.toMatrix_comp stdBasis stdBasis,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    LinearMap.det_toMatrix]
  change Real.sqrt (L.det * (LinearMap.BilinForm.toMatrix stdBasis B).det * L.det) = _
  rw [show L.det * (LinearMap.BilinForm.toMatrix stdBasis B).det * L.det =
    L.det ^ 2 * (LinearMap.BilinForm.toMatrix stdBasis B).det by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

def pullbackInner (g : Metric (M := M)) (x : M) (y : E) : LinearMap.BilinForm ℝ E :=
  (g.inner ((extChartAt I x).symm y)).toBilinForm.comp
    (chartFrame x y).toLinearMap (chartFrame x y).toLinearMap

lemma chartMatrix_eq_toMatrix (g : Metric (M := M)) (x : M) (y : E) :
    chartMatrix g x y = LinearMap.BilinForm.toMatrix stdBasis (pullbackInner g x y) := by
  ext first second
  rw [LinearMap.BilinForm.toMatrix_apply]
  change g.inner ((extChartAt I x).symm y)
    (chartFrame x y (basis first)) (chartFrame x y (basis second)) =
    g.inner ((extChartAt I x).symm y)
      (chartFrame x y (stdBasis first)) (chartFrame x y (stdBasis second))
  simp only [stdBasis, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, basis]

end CKSIntrinsicVolume

end

end OAI
