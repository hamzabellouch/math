import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternModel

namespace OAI

/-! Finite-dimensional Gaussian orthogonal invariance and invariance of the
ordered Wishart eigenvalues, including repeated zero eigenvalues. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

@[irreducible] def gaussianPatternEigenvalues {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) : Fin N → ℝ :=
  (gaussianPatternCoupling_isHermitian 1 z).eigenvalues

lemma gaussianPatternArray_rotation {N m : ℕ} (U : Orthogonal N)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternArray (cavityColumnRotation m (matrixRotation U) z)=
      (U : Matrix (Fin N) (Fin N) ℝ)*gaussianPatternArray z := by
  ext i j
  simp only [gaussianPatternArray,cavityColumnRotation_apply,matrixRotation_apply,Matrix.mul_apply]

lemma gaussianPatternCoupling_rotation {N m : ℕ} (c : ℝ) (U : Orthogonal N)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternCoupling c (cavityColumnRotation m (matrixRotation U) z)=
      (U : Matrix (Fin N) (Fin N) ℝ)*gaussianPatternCoupling c z*
        (U : Matrix (Fin N) (Fin N) ℝ)ᵀ := by
  simp only [gaussianPatternCoupling,gaussianPatternArray_rotation,Matrix.transpose_mul,
    Matrix.mul_assoc,smul_mul_assoc,mul_smul_comm]

lemma gaussianPatternEigenvalues_rotation {N m : ℕ} (U : Orthogonal N)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternEigenvalues (cavityColumnRotation m (matrixRotation U) z)=
      gaussianPatternEigenvalues z := by
  unfold gaussianPatternEigenvalues
  apply ((gaussianPatternCoupling_isHermitian 1 _).eigenvalues_eq_eigenvalues_iff
    (gaussianPatternCoupling_isHermitian 1 z)).mpr
  rw [gaussianPatternCoupling_rotation,Matrix.charpoly_mul_comm,← Matrix.mul_assoc]
  have hU := (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp U.property
  rw [hU,Matrix.one_mul]

lemma gaussianPattern_rotate_hasLaw {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (P : Measure Ω) (Z : Ω → EuclideanSpace ℝ (Fin N × Fin m))
    (hZ : HasLaw Z (stdGaussian _) P) (U : Orthogonal N) :
    HasLaw (fun ω => cavityColumnRotation m (matrixRotation U) (Z ω)) (stdGaussian _) P := by
  have hR : HasLaw (cavityColumnRotation m (matrixRotation U)) (stdGaussian _) (stdGaussian _) :=
    ⟨(cavityColumnRotation m (matrixRotation U)).continuous.aemeasurable,
      cavityColumnRotation_gaussian (matrixRotation U)⟩
  exact hR.fun_comp hZ

end InvariantIsing

end

end OAI
