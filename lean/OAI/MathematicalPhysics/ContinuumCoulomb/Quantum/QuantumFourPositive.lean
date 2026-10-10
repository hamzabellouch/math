import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourGapCertificate
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourIsometry
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalInput
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOperatorQuadratic

namespace OAI

/-! The checked rational certificate is nonnegative on all complex states. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourSymmetricColumn : Matrix (Fin 16) (Fin 5) ℚ :=
  fun s k => if qmaFourWeight s = k then 1 else 0

theorem qmaFourSymmetricRational_factor :
    qmaFourSymmetricColumn*Matrix.diagonal qmaFourSymmetricWeights*qmaFourSymmetricColumn.transpose =
      qmaFourSymmetricRational := by
  ext s t
  simp only [Matrix.mul_apply,Matrix.transpose_apply,qmaFourSymmetricColumn]
  by_cases h : qmaFourWeight s = qmaFourWeight t
  · simp [qmaFourSymmetricRational,← h]
  · simp only [qmaFourSymmetricRational,h,ite_false]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hsk : qmaFourWeight s = k
    · have htk : qmaFourWeight t ≠ k := fun ht => h (hsk.trans ht.symm)
      simp [hsk,htk]
    · simp [hsk]

theorem qmaRatMatrix_adjoint {α β : Type*} (M : Matrix α β ℚ) :
    (M.map (Rat.castHom ℂ)).conjTranspose = M.transpose.map (Rat.castHom ℂ) := by
  ext a b
  simp [Matrix.conjTranspose_apply,Matrix.transpose_apply]

def qmaFourSymmetricColumnComplex : Matrix (Fin 16) (Fin 5) ℂ :=
  qmaFourSymmetricColumn.map (Rat.castHom ℂ)

def qmaFourSymmetricDiagonal : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal (fun k => ((qmaFourSymmetricWeights k:ℝ):ℂ))

theorem qmaFourSymmetricDiagonal_cast :
    (Matrix.diagonal qmaFourSymmetricWeights).map (Rat.castHom ℂ) = qmaFourSymmetricDiagonal := by
  ext a b
  by_cases h : a = b
  · subst b
    simp only [Matrix.map_apply,Matrix.diagonal_apply,ite_true,qmaFourSymmetricDiagonal]
    norm_cast
  · simp [h,qmaFourSymmetricDiagonal]

theorem qmaFourSymmetricComplex_factor :
    qmaFourSymmetricRational.map (Rat.castHom ℂ) = qmaFourSymmetricColumnComplex*
      qmaFourSymmetricDiagonal*qmaFourSymmetricColumnComplex.conjTranspose := by
  rw [← qmaFourSymmetricRational_factor,Matrix.map_mul,Matrix.map_mul,
    qmaFourSymmetricDiagonal_cast]
  rw [qmaFourSymmetricColumnComplex,qmaRatMatrix_adjoint]

theorem qmaFourSymmetric_nonneg (x : EuclideanSpace ℂ (Fin 16)) :
    0 ≤ qmaQuadratic (qmaFourSymmetricRational.map (Rat.castHom ℂ)) (fun i => x i) := by
  rw [qmaFourSymmetricComplex_factor]
  have he := qmaQuadratic_sandwich qmaFourSymmetricColumnComplex.conjTranspose qmaFourSymmetricDiagonal x
  rw [Matrix.conjTranspose_conjTranspose] at he
  rw [he,← qmaQuadratic_operator]
  unfold qmaFourSymmetricDiagonal
  rw [qmaQuadratic_diagonal_real]
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg _ (Complex.normSq_nonneg _)
  fin_cases k <;> norm_num [qmaFourSymmetricWeights]

def qmaFourProjection : Matrix (Fin 16) (Fin 16) ℂ := qmaFourProjectionRational.map (Rat.castHom ℂ)
def qmaFourPenalty : Matrix (Fin 16) (Fin 16) ℂ := qmaFourPenaltyRational.map (Rat.castHom ℂ)

theorem qmaFourGap_complex : qmaFourPenalty-(4:ℂ) • (1-qmaFourProjection) =
    qmaFourSymmetricRational.map (Rat.castHom ℂ) := by
  rw [← qmaFourGapRational_factor]
  ext s t
  simp only [qmaFourPenalty,qmaFourProjection,qmaFourGapRational,Matrix.map_apply,
    Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,map_sub,map_mul,map_ofNat,Matrix.one_apply]
  by_cases h : s = t <;> simp [h]

theorem qmaFourGap_form (x : EuclideanSpace ℂ (Fin 16)) :
    4*(qmaQuadratic (1 : Matrix (Fin 16) (Fin 16) ℂ) (fun i => x i)-
      qmaQuadratic qmaFourProjection (fun i => x i)) ≤ qmaQuadratic qmaFourPenalty (fun i => x i) := by
  have h := qmaFourSymmetric_nonneg x
  rw [← qmaFourGap_complex,qmaQuadratic_sub] at h
  have hs : qmaQuadratic ((4:ℂ) • (1-qmaFourProjection)) (fun i => x i) =
      4*qmaQuadratic (1-qmaFourProjection) (fun i => x i) := by
    simpa only [Complex.ofReal_ofNat] using
      qmaQuadratic_smul (1-qmaFourProjection) (4:ℝ) (fun i => x i)
  rw [hs,qmaQuadratic_sub] at h
  linarith

end ContinuumCoulomb

end

end OAI
