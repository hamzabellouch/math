import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorOrthogonal
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTensorPairLinear
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourCounterterm

namespace OAI

/-! Factorized Heisenberg couplings in the full many-block tensor code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

def qmaFourTensorWeighted (i j : Fin n) (a b : Fin 4 → ℝ) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  ∑ p, ∑ q, ((a p*b q:ℝ):ℂ) • qmaFourTensorCross i j p q

theorem qmaFourTensorWeighted_orthogonal (i j : Fin n) (hij : i ≠ j) (a b : Fin 4 → ℝ) :
    (qmaFourTensorEncoding n).conjTranspose*(qmaFourTensorWeighted i j a b*qmaFourTensorEncoding n) = 0 := by
  simp only [qmaFourTensorWeighted,Matrix.sum_mul,Matrix.smul_mul,Matrix.mul_sum,Matrix.mul_smul,
    qmaFourTensorCross_orthogonal i j hij,smul_zero,Finset.sum_const_zero]

theorem qmaFourTensorWeighted_excitation (i j : Fin n) (hij : i ≠ j) (a b : Fin 4 → ℝ) :
    qmaFourTensorPenalty n*(qmaFourTensorWeighted i j a b*qmaFourTensorEncoding n) =
      (8:ℂ) • (qmaFourTensorWeighted i j a b*qmaFourTensorEncoding n) := by
  simp only [qmaFourTensorWeighted,Matrix.sum_mul,Matrix.smul_mul,Matrix.mul_sum,Matrix.mul_smul,
    qmaFourTensorCross_excitation i j hij]
  simp only [Finset.smul_sum,smul_comm (8:ℂ)]

theorem qmaFourTensorWeighted_gram (i j : Fin n) (hij : i ≠ j) (a b : Fin 4 → ℝ) :
    (qmaFourTensorWeighted i j a b*qmaFourTensorEncoding n).conjTranspose*
      (qmaFourTensorWeighted i j a b*qmaFourTensorEncoding n) =
        (3:ℂ) • qmaPairMatrix i j (qmaFourWeightedCorrelation a) (qmaFourWeightedCorrelation b) := by
  simp only [qmaFourTensorWeighted,Matrix.sum_mul,Matrix.smul_mul,Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul,Matrix.mul_sum,Matrix.mul_smul,smul_smul,
    Complex.star_def,Complex.conj_ofReal,qmaFourTensorCross_gram i j hij,qmaFourWeightedCorrelation,
    qmaPairMatrix_sum_left _ _ hij,qmaPairMatrix_sum_right _ _ hij,
    qmaPairMatrix_smul_left _ _ hij,qmaPairMatrix_smul_right _ _ hij,Finset.smul_sum,smul_smul]
  have hswap (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 →
      Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
      (∑ p, ∑ q, ∑ r, ∑ s, f p q r s) = ∑ p, ∑ r, ∑ q, ∑ s, f p q r s := by
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
  rw [hswap]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro r _
  rw [qmaFourCorrelation_comm s q,qmaFourCorrelation_comm r p]
  congr 1
  push_cast
  ring

theorem qmaFourTensorWeighted_distinct (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hne : ({i,j} : Finset (Fin n)) ≠ {k,l}) (a b c d : Fin 4 → ℝ) :
    (qmaFourTensorWeighted i j a b*qmaFourTensorEncoding n).conjTranspose*
      (qmaFourTensorWeighted k l c d*qmaFourTensorEncoding n) = 0 := by
  simp only [qmaFourTensorWeighted,Matrix.sum_mul,Matrix.smul_mul,Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul,Matrix.mul_sum,Matrix.mul_smul,
    qmaFourTensorCross_distinct i j k l hij hkl hne,smul_zero,Finset.sum_const_zero]

end ContinuumCoulomb

end

end OAI
