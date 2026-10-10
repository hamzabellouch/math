import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourCross
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorGraph

namespace OAI

/-! Factorized real Heisenberg couplings between two four-spin blocks. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

def qmaFourWeightedCorrelation (a : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i, ∑ k, ((a i*a k:ℝ):ℂ) • qmaFourCorrelation i k

def qmaFourWeightedCross (a b : Fin 4 → ℝ) :
    Matrix (Fin 16 × Fin 16) (Fin 16 × Fin 16) ℂ :=
  ∑ i, ∑ j, ((a i*b j:ℝ):ℂ) • qmaFourCross i j

theorem qmaFourWeightedCross_orthogonal (a b : Fin 4 → ℝ) :
    qmaFourDoubleEncoding.conjTranspose*qmaFourWeightedCross a b*qmaFourDoubleEncoding = 0 := by
  simp only [qmaFourWeightedCross,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
  simp only [qmaFourCross_orthogonal,smul_zero,Finset.sum_const_zero]

theorem qmaFourWeightedCross_excitation (a b : Fin 4 → ℝ) :
    qmaFourDoublePenalty*(qmaFourWeightedCross a b*qmaFourDoubleEncoding) =
      (8:ℂ) • (qmaFourWeightedCross a b*qmaFourDoubleEncoding) := by
  simp only [qmaFourWeightedCross,Matrix.mul_sum,Matrix.sum_mul,Matrix.smul_mul,
    Matrix.mul_smul,qmaFourCross_excitation]
  simp only [Finset.smul_sum,smul_comm (8:ℂ)]

theorem qmaFourWeightedCross_gram (a b : Fin 4 → ℝ) :
    (qmaFourWeightedCross a b*qmaFourDoubleEncoding).conjTranspose*
      (qmaFourWeightedCross a b*qmaFourDoubleEncoding) =
        (3:ℂ) • (qmaFourWeightedCorrelation a ⊗ₖ qmaFourWeightedCorrelation b) := by
  simp only [qmaFourWeightedCross,Matrix.sum_mul,Matrix.smul_mul,Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul,Matrix.mul_sum,Matrix.mul_smul,smul_smul,
    Complex.star_def,Complex.conj_ofReal,qmaFourCross_gram,qmaFourWeightedCorrelation,
    MediatorGraph.sum_kronecker,MediatorGraph.kronecker_sum,Matrix.smul_kronecker,
    Matrix.kronecker_smul,Finset.smul_sum,smul_smul]
  have hswap (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
      (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ j, ∑ l, ∑ i, ∑ k, f i j k l := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ j, ∑ i, ∑ l, ∑ k, f i j k l := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
  rw [hswap]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [qmaFourCorrelation_comm k i,qmaFourCorrelation_comm l j]
  congr 1
  push_cast
  ring

end ContinuumCoulomb

end

end OAI
