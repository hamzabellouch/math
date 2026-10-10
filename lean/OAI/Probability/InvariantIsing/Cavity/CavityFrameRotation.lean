import OAI.Probability.InvariantIsing.Cavity.CavityFrameAlgebra

namespace OAI

/-! Orthogonal equivariance of the Gaussian frame normalization. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavityGram_left_orthogonal {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.transpose * U = 1) :
    (U * A).transpose * (U * A) = A.transpose * A := by
  rw [Matrix.transpose_mul]
  calc
    A.transpose * U.transpose * (U * A) = A.transpose * (U.transpose * U) * A := by
      simp only [Matrix.mul_assoc]
    _ = A.transpose * A := by rw [hU, Matrix.mul_one]

lemma cavityNormalizeFrame_left_orthogonal {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.transpose * U = 1) :
    cavityNormalizeFrame (U * A) = U * cavityNormalizeFrame A := by
  simp only [cavityNormalizeFrame, cavityGram_left_orthogonal A U hU, Matrix.mul_assoc]


end InvariantIsing

end

end OAI
