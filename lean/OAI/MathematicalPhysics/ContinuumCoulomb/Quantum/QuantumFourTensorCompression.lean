import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorCross

namespace OAI

/-! Exact one-block and two-block compression in the full tensor encoding. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

theorem qmaFourTensor_site_compression (i : Fin n) (A : Matrix (Fin 16) (Fin 16) ℂ) :
    (qmaFourTensorEncoding n).conjTranspose*qmaSiteMatrix i A*qmaFourTensorEncoding n =
      qmaSiteMatrix i (qmaFourEncoding.conjTranspose*A*qmaFourEncoding) := by
  simp only [qmaFourTensorEncoding,qmaSiteMatrix,qmaTensorMatrix_star,qmaTensorMatrix_mul]
  congr 1
  funext k
  by_cases h : k = i
  · simp only [h,ite_true]
  · simp only [h,ite_false,Matrix.mul_one,qmaFourEncoding_gram]

theorem qmaFourTensor_pair_compression (i j : Fin n)
    (A B : Matrix (Fin 16) (Fin 16) ℂ) :
    (qmaFourTensorEncoding n).conjTranspose*qmaPairMatrix i j A B*qmaFourTensorEncoding n =
      qmaPairMatrix i j (qmaFourEncoding.conjTranspose*A*qmaFourEncoding)
        (qmaFourEncoding.conjTranspose*B*qmaFourEncoding) := by
  simp only [qmaFourTensorEncoding,qmaPairMatrix,qmaTensorMatrix_star,qmaTensorMatrix_mul]
  congr 1
  funext k
  by_cases hi : k = i
  · simp only [hi,ite_true]
  · by_cases hj : k = j
    · subst k
      simp only [hi,ite_false,ite_true]
    · simp only [hi,hj,ite_false,Matrix.mul_one,qmaFourEncoding_gram]

end ContinuumCoulomb

end

end OAI
