import OAI.MeasureTheory.Falconer.Angular.GraphAngularCoordinates
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal

abbrev GraphLiftSpace := Fin 3 → ℝ

noncomputable def graphLiftMap (p : GraphLiftSpace) : GraphLiftSpace :=
  ![p 0*Real.sqrt (1+(p 2)^2)/2, p 1+Real.arctan (p 2), p 1-Real.arctan (p 2)]

noncomputable def graphLiftMatrix (p : GraphLiftSpace) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.sqrt (1+(p 2)^2)/2, 0, p 0*p 2/(2*Real.sqrt (1+(p 2)^2));
     0, 1, 1/(1+(p 2)^2);
     0, 1, -(1/(1+(p 2)^2))]

noncomputable def graphLiftDerivative (p : GraphLiftSpace) : GraphLiftSpace →L[ℝ] GraphLiftSpace :=
  (Matrix.toLin' (graphLiftMatrix p)).toContinuousLinearMap

theorem graphLiftMap_hasFDerivAt (p : GraphLiftSpace) :
    HasFDerivAt graphLiftMap (graphLiftDerivative p) p := by
  have h₀ := hasFDerivAt_apply (𝕜 := ℝ) 0 p
  have h₁ := hasFDerivAt_apply (𝕜 := ℝ) 1 p
  have h₂ := hasFDerivAt_apply (𝕜 := ℝ) 2 p
  have hs := ((h₂.pow 2).const_add 1).sqrt (by positivity : 1+(p 2)^2 ≠ 0)
  have ha := (Real.hasDerivAt_arctan (p 2)).comp_hasFDerivAt p h₂
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert! (h₀.mul hs).mul_const (1/2 : ℝ) using 1 <;>
      ext v <;>
      simp [graphLiftMap, graphLiftDerivative, graphLiftMatrix, Matrix.toLin'_apply,
      dotProduct, Fin.sum_univ_three]
    <;> ring
  · convert! h₁.add ha using 1
    ext v
    simp [graphLiftDerivative, graphLiftMatrix, Matrix.toLin'_apply,
      dotProduct, Fin.sum_univ_three]
  · convert! h₁.sub ha using 1
    ext v
    simp [graphLiftDerivative, graphLiftMatrix, Matrix.toLin'_apply,
      dotProduct, Fin.sum_univ_three, sub_eq_add_neg]

theorem graphLiftDerivative_det (p : GraphLiftSpace) :
    (graphLiftDerivative p).det = -(Real.sqrt (1+(p 2)^2))⁻¹ := by
  have hs : Real.sqrt (1+(p 2)^2) ≠ 0 := by positivity
  have hq : 1+(p 2)^2 ≠ 0 := by positivity
  have he := Real.sq_sqrt (by positivity : 0 ≤ 1+(p 2)^2)
  simp only [graphLiftDerivative, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin']
  simp [graphLiftMatrix, Matrix.det_fin_three]
  field_simp
  nlinarith

theorem graphLiftMap_injective : Function.Injective graphLiftMap := by
  intro p q he
  have h₀ := congrFun he 0
  have h₁ := congrFun he 1
  have h₂ := congrFun he 2
  simp only [graphLiftMap, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at h₀ h₁ h₂
  change p 1-Real.arctan (p 2) = q 1-Real.arctan (q 2) at h₂
  have hz : p 2 = q 2 := Real.arctan_injective (by linarith)
  have hφ : p 1 = q 1 := by linarith
  have hs : Real.sqrt (1+(q 2)^2) ≠ 0 := by positivity
  rw [hz] at h₀
  have hr : p 0 = q 0 := mul_right_cancel₀ hs (by linarith only [h₀])
  ext i
  fin_cases i <;> assumption

theorem graphLiftMap_lintegral (S : Set GraphLiftSpace) (hS : MeasurableSet S)
    (f : GraphLiftSpace → ℝ≥0∞) :
    (∫⁻ q in graphLiftMap '' S, f q) =
      ∫⁻ p in S, ENNReal.ofReal ((Real.sqrt (1+(p 2)^2))⁻¹) * f (graphLiftMap p) := by
  have he := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (fun p (_ : p ∈ S) => (graphLiftMap_hasFDerivAt p).hasFDerivWithinAt)
    graphLiftMap_injective.injOn f
  simpa only [graphLiftDerivative_det, abs_neg, abs_of_nonneg
    (inv_nonneg.mpr (Real.sqrt_nonneg _))] using he

end PlanarFalconer

end OAI
