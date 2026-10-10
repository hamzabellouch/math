import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourCorrelation

namespace OAI

/-! Exact second-order columns for a Heisenberg edge between two encoded blocks. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

def qmaFourDoubleEncoding : Matrix (Fin 16 × Fin 16) (Fin 2 × Fin 2) ℂ :=
  qmaFourEncoding ⊗ₖ qmaFourEncoding

def qmaFourDoublePenalty : Matrix (Fin 16 × Fin 16) (Fin 16 × Fin 16) ℂ :=
  qmaFourPenalty ⊗ₖ (1 : Matrix (Fin 16) (Fin 16) ℂ)+
    (1 : Matrix (Fin 16) (Fin 16) ℂ) ⊗ₖ qmaFourPenalty

def qmaFourCross (i j : Fin 4) : Matrix (Fin 16 × Fin 16) (Fin 16 × Fin 16) ℂ :=
  ∑ μ : Fin 3, qmaFourSpin i μ ⊗ₖ qmaFourSpin j μ

theorem qmaFourDoubleEncoding_gram :
    qmaFourDoubleEncoding.conjTranspose*qmaFourDoubleEncoding = 1 := by
  rw [qmaFourDoubleEncoding,Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,
    qmaFourEncoding_gram,Matrix.one_kronecker_one]

theorem qmaFourCross_column (i j : Fin 4) :
    qmaFourCross i j*qmaFourDoubleEncoding =
      ∑ μ : Fin 3, (qmaFourSpin i μ*qmaFourEncoding) ⊗ₖ (qmaFourSpin j μ*qmaFourEncoding) := by
  simp only [qmaFourCross,qmaFourDoubleEncoding,Matrix.sum_mul,← Matrix.mul_kronecker_mul]

theorem qmaFourCross_orthogonal (i j : Fin 4) :
    qmaFourDoubleEncoding.conjTranspose*qmaFourCross i j*qmaFourDoubleEncoding = 0 := by
  rw [Matrix.mul_assoc,qmaFourCross_column,qmaFourDoubleEncoding,Matrix.conjTranspose_kronecker]
  simp only [Matrix.mul_sum,← Matrix.mul_kronecker_mul,← Matrix.mul_assoc,
    qmaFourSpin_orthogonal,Matrix.zero_kronecker,Finset.sum_const_zero]

theorem qmaFourCross_excitation (i j : Fin 4) :
    qmaFourDoublePenalty*(qmaFourCross i j*qmaFourDoubleEncoding) =
      (8:ℂ) • (qmaFourCross i j*qmaFourDoubleEncoding) := by
  rw [qmaFourCross_column]
  simp only [qmaFourDoublePenalty,Matrix.mul_sum,Matrix.add_mul,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul,qmaFourSpin_excitation,
    Matrix.smul_kronecker,Matrix.kronecker_smul,← add_smul]
  simp only [show (4:ℂ)+4 = 8 by norm_num,Finset.smul_sum]

theorem qmaFourCross_gram (i j k l : Fin 4) :
    (qmaFourCross i j*qmaFourDoubleEncoding).conjTranspose*
      (qmaFourCross k l*qmaFourDoubleEncoding) =
        (3:ℂ) • (qmaFourCorrelation i k ⊗ₖ qmaFourCorrelation j l) := by
  rw [qmaFourCross_column,qmaFourCross_column]
  simp only [Matrix.conjTranspose_sum,Matrix.sum_mul,Matrix.mul_sum,
    Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,qmaFourSpin_correlation]
  have he (μ ν : Fin 3) :
      (if μ = ν then qmaFourCorrelation i k else 0) ⊗ₖ
        (if μ = ν then qmaFourCorrelation j l else 0) =
          if μ = ν then qmaFourCorrelation i k ⊗ₖ qmaFourCorrelation j l else 0 := by
    by_cases h : μ = ν <;> simp [h]
  simp only [he]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.sum_const]
  norm_cast

end ContinuumCoulomb

end

end OAI
