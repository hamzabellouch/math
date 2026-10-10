import OAI.Geometry.Relativity.CKS.SchwarzschildRoundMetric
import OAI.Geometry.Relativity.CKS.SphereConeAlgebra

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
local instance sphereConeChartFinrank : Fact (Module.finrank ℝ E3 = 2+1) := ⟨by simp⟩

def sphereParam (p : Sphere) (y : E2) : E3 := ((extChartAt I2 p).symm y).val
def sphereParamDeriv (p : Sphere) (y : E2) : E2 →L[ℝ] E3 :=
  (sphereDerivative ((extChartAt I2 p).symm y)).comp (CKSSurfaceVolume.chartFrame p y)
lemma sphereParam_norm (p : Sphere) (y : E2) : ‖sphereParam p y‖ = 1 := by
  simpa only [sphereParam,Metric.mem_sphere,dist_zero_right] using ((extChartAt I2 p).symm y).property
lemma sphereParamDeriv_orthogonal (p : Sphere) (y : E2) (v : E2) :
    ⟪sphereParam p y,sphereParamDeriv p y v⟫_ℝ = 0 := by
  have orthogonalRange : (sphereDerivative ((extChartAt I2 p).symm y)).range =
      (ℝ ∙ (((extChartAt I2 p).symm y).val : E3))ᗮ := by
    convert! range_mvfderiv_subtypeVal (n := 2) ((extChartAt I2 p).symm y)
  have hv : sphereParamDeriv p y v ∈ (ℝ ∙ sphereParam p y)ᗮ := by
    change sphereParamDeriv p y v ∈ (ℝ ∙ (((extChartAt I2 p).symm y).val : E3))ᗮ
    rw [← orthogonalRange]
    exact ⟨CKSSurfaceVolume.chartFrame p y v,rfl⟩
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hv
lemma sphereParam_hasFDerivAt (p : Sphere) {y : E2}
    (hy : y ∈ (extChartAt I2 p).target) : HasFDerivAt (sphereParam p) (sphereParamDeriv p y) y := by
  have hi := (mdifferentiableWithinAt_extChartAt_symm (I := I2) hy).hasMFDerivWithinAt
  have hc := ((contMDiff_coe_sphere (n := 2) (m := ∞) ((extChartAt I2 p).symm y)).mdifferentiableAt
    (by simp)).hasMFDerivAt
  have h := hc.comp_hasMFDerivWithinAt y hi
  have hh : HasFDerivWithinAt (sphereParam p) (sphereParamDeriv p y) univ y := by
    have hh := h.hasFDerivWithinAt
    change HasFDerivWithinAt (sphereParam p) (sphereParamDeriv p y) (range (id : E2 → E2)) y at hh
    simpa only [range_id] using hh
  exact hh.hasFDerivAt (by simp)

lemma sphereParamDeriv_density (p : Sphere) (y : E2) :
    Real.sqrt (Matrix.gram ℝ (fun i : Fin 2 => sphereParamDeriv p y
      (EuclideanSpace.basisFun (Fin 2) ℝ i))).det =
      CKSSurfaceVolume.chartDensity sphereMetric.toContinuousRiemannianMetric p y := by
  congr 2
  ext i j
  simp only [CKSSurfaceVolume.chartMatrix,Matrix.gram_apply,EuclideanSpace.basisFun_apply]
  rfl

def sphereCone (p : Sphere) (z : E3) : E3 := (z 0) • sphereParam p (dropPlane z)
def sphereConeDeriv (p : Sphere) (z : E3) : E3 →L[ℝ] E3 :=
  coneLinear (z 0) (sphereParam p (dropPlane z)) (sphereParamDeriv p (dropPlane z))
lemma sphereCone_hasFDerivAt (p : Sphere) {z : E3}
    (hz : dropPlane z ∈ (extChartAt I2 p).target) :
    HasFDerivAt (sphereCone p) (sphereConeDeriv p z) z := by
  have h := firstCoordinate.hasFDerivAt.smul
    ((sphereParam_hasFDerivAt p hz).comp z dropPlane.hasFDerivAt)
  change HasFDerivAt (sphereCone p)
    ((z 0) • (sphereParamDeriv p (dropPlane z)).comp dropPlane +
      firstCoordinate.smulRight (sphereParam p (dropPlane z))) z at h
  have he : ((z 0) • (sphereParamDeriv p (dropPlane z)).comp dropPlane +
      firstCoordinate.smulRight (sphereParam p (dropPlane z))) = sphereConeDeriv p z := by
    apply ContinuousLinearMap.ext
    intro v
    change (z 0) • sphereParamDeriv p (dropPlane z) (dropPlane v) +
      (v 0) • sphereParam p (dropPlane z) =
      (v 0) • sphereParam p (dropPlane z) + (z 0) • sphereParamDeriv p (dropPlane z) (dropPlane v)
    exact add_comm _ _
  rw [he] at h
  exact h
lemma sphereCone_det (p : Sphere) (z : E3) :
    |(sphereConeDeriv p z).det| = (z 0)^2 *
      CKSSurfaceVolume.chartDensity sphereMetric.toContinuousRiemannianMetric p (dropPlane z) := by
  rw [sphereConeDeriv,abs_det_coneLinear _ _ _ (sphereParam_norm _ _) (sphereParamDeriv_orthogonal _ _),
    sphereParamDeriv_density]

end CKSSchwarzschild

end

end OAI
