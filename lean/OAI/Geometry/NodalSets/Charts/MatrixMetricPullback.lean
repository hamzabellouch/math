import OAI.Geometry.NodalSets.Coefficients.IntrinsicCoefficientSmooth
import OAI.Geometry.NodalSets.Coefficients.RoundCoefficientJets

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped RealInnerProductSpace ContDiff
noncomputable section

lemma matrixCovariant_eq_of_entries (B : Matrix (Fin 4) (Fin 4) ℝ)
    (g : BaseModel →L[ℝ] BaseModel →L[ℝ] ℝ)
    (he : ∀ i j, g (EuclideanSpace.basisFun (Fin 4) ℝ j)
      (EuclideanSpace.basisFun (Fin 4) ℝ i) = B i j) : matrixCovariant B = g := by
  ext v w
  rw [matrixCovariant_apply]
  have hv := (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v
  have hw := (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr w
  conv_rhs => rw [← hv,← hw]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul,he]
  simp only [mulVec,dotProduct,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [mul_comm,mul_assoc]

lemma matrixCovariant_horizontal (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    (ρ : ℝ) (hρ : 0 < ρ) (p : Base) (z : BaseModel) :
    matrixCovariant (sphereWeightedChartMatrix A ρ p z) =
      bilinearPullback (ambientMatrixForm (weightedBaseMatrix A ρ)) (sphereChartDerivative p z) := by
  apply matrixCovariant_eq_of_entries
  intro i j
  rw [bilinearPullback_apply,ambientMatrixForm_symm _ (weightedBaseMatrix_posDef hA hρ).1,
    sphereWeightedChartMatrix_apply]

lemma matrixCovariant_round (p : Base) (z : BaseModel) :
    matrixCovariant (sphereRoundChartMatrix p z) = roundChartMetric p z := by
  have h := matrixCovariant_horizontal (1 : Matrix (Fin 5) (Fin 5) ℝ) PosDef.one 1 zero_lt_one p z
  have hm : sphereWeightedChartMatrix (1 : Matrix (Fin 5) (Fin 5) ℝ) 1 p z = sphereRoundChartMatrix p z := by
    simp [sphereWeightedChartMatrix,sphereRoundChartMatrix,weightedBaseMatrix]
  rw [hm] at h
  have hform : ambientMatrixForm (weightedBaseMatrix (1 : Matrix (Fin 5) (Fin 5) ℝ) 1) =
      ambientRoundBilinear := by
    simp only [weightedBaseMatrix,inv_one,one_smul]
    ext v w
    rw [ambientMatrixForm_dot,one_mulVec]
    change WithLp.ofLp v ⬝ᵥ WithLp.ofLp w = ⟪v,w⟫
    simp [PiLp.inner_apply,dotProduct,mul_comm]
  rw [hform] at h
  exact h

lemma matrixCovariant_inverse (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : IsUnit B.det) :
    ContinuousLinearMap.inverse (matrixCovariant B) = matrixContravariant B⁻¹ := by
  apply ContinuousLinearMap.inverse_eq
  · ext α v
    have h : baseCovectorCoordinates (matrixCovariant B (matrixContravariant B⁻¹ α)) =
        baseCovectorCoordinates α := by
      rw [matrixCovariant_coordinates,matrixContravariant_coordinates,mulVec_mulVec,
        mul_nonsing_inv B hB,one_mulVec]
    exact congrArg (fun β : BaseModel →L[ℝ] ℝ ↦ β v) (baseCovectorCoordinates_injective h)
  · ext v i
    have h := matrixContravariant_coordinates B⁻¹ (matrixCovariant B v)
    rw [matrixCovariant_coordinates,mulVec_mulVec,nonsing_inv_mul B hB,one_mulVec] at h
    exact congrFun h i

lemma roundCoefficients_matrix (z : BaseModel) :
    roundCoefficients z = (matrixContravariant (sphereRoundChartMatrix seedPoint z)⁻¹,1) := by
  unfold roundCoefficients
  rw [← matrixCovariant_round,matrixCovariant_inverse _ (isUnit_iff_ne_zero.mpr
    (sphereRoundChartMatrix_posDef seedPoint (by rw [centeredSphereChart_target]; trivial)).det_pos.ne')]

lemma roundCoefficients_matrix_fderiv (z : BaseModel) :
    fderiv ℝ roundCoefficients z =
      fderiv ℝ (fun w ↦ (matrixContravariant (sphereRoundChartMatrix seedPoint w)⁻¹,(1:ℝ))) z := by
  have he : roundCoefficients = fun w ↦ (matrixContravariant (sphereRoundChartMatrix seedPoint w)⁻¹,(1:ℝ)) :=
    funext roundCoefficients_matrix
  rw [he]

end
end Yau.Target

end OAI
