import OAI.Geometry.NodalSets.Charts.BaseChartFlux
import OAI.Geometry.NodalSets.Charts.CenteredSphereMetricLemmas
import OAI.Geometry.NodalSets.Elliptic.IndependentWeightedSmooth

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma centeredSphereRoundDet_hasFDerivAt (p : Base) :
    HasFDerivAt (fun y ↦ (sphereRoundChartMatrix p y).det) (0 : BaseModel →L[ℝ] ℝ) 0 := by
  have hc : ContDiff ℝ ∞ (fun A : Fin 4 → Fin 4 → ℝ ↦ Matrix.det A) :=
    matrix_det_smooth (fun A : Fin 4 → Fin 4 → ℝ ↦ A)
      (fun i j ↦ by fun_prop)
  have h := ((hc.differentiable (by simp)) (sphereRoundChartMatrix p 0)).hasFDerivAt.comp 0
    (centeredSphereRoundMatrix_hasFDerivAt p)
  convert! h using 1
  exact (ContinuousLinearMap.comp_zero _).symm

lemma centeredSphereRoundInv_hasFDerivAt (p : Base) (i j : Fin 4) :
    HasFDerivAt (fun y ↦ (sphereRoundChartMatrix p y)⁻¹ i j) (0 : BaseModel →L[ℝ] ℝ) 0 := by
  have hc : ContDiff ℝ ∞ (fun A : Fin 4 → Fin 4 → ℝ ↦ Matrix.adjugate A i j) :=
    matrix_adjugate_smooth (fun A : Fin 4 → Fin 4 → ℝ ↦ A)
      (fun k l ↦ by fun_prop) i j
  have ha : HasFDerivAt (fun y ↦ (sphereRoundChartMatrix p y).adjugate i j)
      (0 : BaseModel →L[ℝ] ℝ) 0 := by
    convert! ((hc.differentiable (by simp)) (sphereRoundChartMatrix p 0)).hasFDerivAt.comp 0
      (centeredSphereRoundMatrix_hasFDerivAt p) using 1
    exact (ContinuousLinearMap.comp_zero _).symm
  have hd : HasFDerivAt (fun y ↦ ((sphereRoundChartMatrix p y).det)⁻¹)
      (0 : BaseModel →L[ℝ] ℝ) 0 := by
    have h := (hasDerivAt_inv (by rw [centeredSphereRoundMatrix,Matrix.det_one]; norm_num)).comp_hasFDerivAt 0
      (centeredSphereRoundDet_hasFDerivAt p)
    convert! h using 1
    simp
  have h := hd.mul ha
  convert! h using 1 <;> simp [Matrix.inv_def,Ring.inverse_eq_inv,funext_iff]

lemma centeredRoundChartDensity (p : Base) : roundChartDensity p 0 = 1 := by
  simp [roundChartDensity,centeredSphereRoundMatrix]

lemma centeredRoundChartDensity_hasFDerivAt (p : Base) :
    HasFDerivAt (roundChartDensity p) (0 : BaseModel →L[ℝ] ℝ) 0 := by
  have h := (Real.hasDerivAt_sqrt (by rw [centeredSphereRoundMatrix,Matrix.det_one]; norm_num)).comp_hasFDerivAt 0
    (centeredSphereRoundDet_hasFDerivAt p)
  convert! h using 1
  simp

end
end Yau.Target

end OAI
