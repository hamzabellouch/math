import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorNorm
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorFamily

namespace OAI

/-! Bounds and excitation identities for the whole physical edge family. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

theorem qmaFourTensorCoupling_orthogonal (i j : Fin n) (hij : i ≠ j) (a b : Fin 2) (t : ℝ) :
    (qmaFourTensorEncoding n).conjTranspose*(qmaFourTensorCoupling i j a b t*qmaFourTensorEncoding n) = 0 := by
  simp only [qmaFourTensorCoupling,Matrix.smul_mul,Matrix.mul_smul,
    qmaFourTensorWeighted_orthogonal i j hij,smul_zero]

theorem qmaFourTensorCoupling_excitation (i j : Fin n) (hij : i ≠ j) (a b : Fin 2) (t : ℝ) :
    qmaFourTensorPenalty n*(qmaFourTensorCoupling i j a b t*qmaFourTensorEncoding n) =
      (8:ℂ) • (qmaFourTensorCoupling i j a b t*qmaFourTensorEncoding n) := by
  simp only [qmaFourTensorCoupling,Matrix.smul_mul,Matrix.mul_smul,
    qmaFourTensorWeighted_excitation i j hij,smul_comm (8:ℂ)]

theorem qmaFourTensorFamily_orthogonal (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (hneq : ∀ e, left e ≠ right e) :
    (qmaFourTensorEncoding n).conjTranspose*
      (qmaFourTensorFamilyCoupling left right a b t*qmaFourTensorEncoding n) = 0 := by
  simp only [qmaFourTensorFamilyCoupling,Matrix.sum_mul,Matrix.mul_sum,
    qmaFourTensorCoupling_orthogonal _ _ (hneq _),Finset.sum_const_zero]

theorem qmaFourTensorFamily_excitation (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (hneq : ∀ e, left e ≠ right e) :
    qmaFourTensorPenalty n*(qmaFourTensorFamilyCoupling left right a b t*qmaFourTensorEncoding n) =
      (8:ℂ) • (qmaFourTensorFamilyCoupling left right a b t*qmaFourTensorEncoding n) := by
  simp only [qmaFourTensorFamilyCoupling,Matrix.sum_mul,Matrix.mul_sum,
    qmaFourTensorCoupling_excitation _ _ (hneq _),Finset.smul_sum]

theorem qmaFourTensorFamily_norm (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ) :
    ‖spinMatrixOperator (qmaFourTensorFamilyCoupling left right a b t)‖ ≤
      7056*(∑ e, (1+|t e|)) := by
  rw [qmaFourTensorFamilyCoupling,spinMatrixOperator_sum,Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ => qmaFourTensorCoupling_norm _ _ _ _ _))

theorem qmaSiteMatrix_commute (i j : Fin n) (hij : i ≠ j) (A B : Matrix (Fin 16) (Fin 16) ℂ) :
    qmaSiteMatrix i A*qmaSiteMatrix j B = qmaSiteMatrix j B*qmaSiteMatrix i A := by
  simp only [qmaSiteMatrix,qmaTensorMatrix_mul]
  congr 1
  funext k
  by_cases hi : k = i
  · subst k
    simp only [ite_true,hij,ite_false,Matrix.mul_one,Matrix.one_mul]
  · by_cases hj : k = j
    · subst k
      simp only [ite_true,Ne.symm hij,ite_false,Matrix.mul_one,Matrix.one_mul]
    · simp only [hi,hj,ite_false]

theorem qmaFourTensorCross_star (i j : Fin n) (hij : i ≠ j) (p q : Fin 4) :
    (qmaFourTensorCross i j p q).conjTranspose = qmaFourTensorCross i j p q := by
  simp only [qmaFourTensorCross,Matrix.conjTranspose_sum,Matrix.conjTranspose_mul,
    qmaSiteMatrix_star,qmaFourSpin_star]
  apply Finset.sum_congr rfl
  intro μ _
  exact qmaSiteMatrix_commute j i (Ne.symm hij) _ _

theorem qmaFourTensorCoupling_star (i j : Fin n) (hij : i ≠ j) (a b : Fin 2) (t : ℝ) :
    (qmaFourTensorCoupling i j a b t).conjTranspose = qmaFourTensorCoupling i j a b t := by
  simp only [qmaFourTensorCoupling,qmaFourTensorWeighted,Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sum,Complex.star_def,Complex.conj_ofReal,qmaFourTensorCross_star i j hij]

theorem qmaFourTensorFamily_star (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (hneq : ∀ e, left e ≠ right e) :
    (qmaFourTensorFamilyCoupling left right a b t).conjTranspose =
      qmaFourTensorFamilyCoupling left right a b t := by
  simp only [qmaFourTensorFamilyCoupling,Matrix.conjTranspose_sum,
    qmaFourTensorCoupling_star _ _ (hneq _)]

end ContinuumCoulomb

end

end OAI
