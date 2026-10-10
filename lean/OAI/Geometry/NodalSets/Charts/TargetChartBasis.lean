import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import OAI.Geometry.NodalSets.Charts.ProductChartPullback

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
noncomputable section

def productIndexEquiv : (Fin 4 ⊕ Fin 1) ≃ Index :=
  finSumFinEquiv.trans (finCongr (by simp [Model]))

def indexedProductFrame : Module.Basis Index ℝ Model :=
  productFrame.reindex productIndexEquiv

def targetFrameChange : Matrix Index Index ℝ := indexedProductFrame.toMatrix frame

def targetFrameVolume : ℝ := |targetFrameChange.det|

lemma targetFrameChange_det_ne_zero : targetFrameChange.det ≠ 0 := by
  have h := congrArg Matrix.det (indexedProductFrame.toMatrix_mul_toMatrix_flip frame)
  rw [det_mul,det_one] at h
  exact (mul_ne_zero_iff.mp (h ▸ one_ne_zero)).1

lemma targetFrameVolume_pos : 0 < targetFrameVolume :=
  abs_pos.mpr targetFrameChange_det_ne_zero

def chartBilinearForm (g : SmoothMetric) (c : PartialEquiv Manifold5 Model) (y : Model) :
    LinearMap.BilinForm ℝ Model :=
  ((g.inner (c.symm y)).toBilinForm).compl₁₂
    (mfderiv 𝓘(ℝ,Model) modelWithCorners c.symm y).toLinearMap
    (mfderiv 𝓘(ℝ,Model) modelWithCorners c.symm y).toLinearMap

lemma metricMatrix_basis_change (g : SmoothMetric) (p : Manifold5) (y : Model) :
    metricMatrix g (extChartAt modelWithCorners p) y =
      targetFrameChange.transpose *
        (productMetricMatrix g p y).submatrix productIndexEquiv.symm productIndexEquiv.symm *
        targetFrameChange := by
  have h := LinearMap.toMatrix₂_mul_basis_toMatrix indexedProductFrame indexedProductFrame
    frame frame (chartBilinearForm g (extChartAt modelWithCorners p) y)
  convert! h.symm using 1
  · ext i j
    simp only [LinearMap.toMatrix₂_apply,chartBilinearForm,metricMatrix]
    rfl
  · congr 2
    ext i j
    simp [LinearMap.toMatrix₂_apply,chartBilinearForm,indexedProductFrame,
      productMetricMatrix,Module.Basis.reindex_apply]
    rfl

lemma metricMatrix_det_basis_change (g : SmoothMetric) (p : Manifold5) (y : Model) :
    (metricMatrix g (extChartAt modelWithCorners p) y).det =
      targetFrameChange.det^2 * (productMetricMatrix g p y).det := by
  rw [metricMatrix_basis_change,det_mul,det_mul,det_transpose,det_submatrix_equiv_self]
  ring

lemma volumeFactor_basis_change (g : SmoothMetric) (p : Manifold5) (y : Model) :
    volumeFactor g (extChartAt modelWithCorners p) y =
      targetFrameVolume * Real.sqrt (productMetricMatrix g p y).det := by
  rw [volumeFactor,metricMatrix_det_basis_change,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs]
  rfl

end
end Yau.Target

end OAI
