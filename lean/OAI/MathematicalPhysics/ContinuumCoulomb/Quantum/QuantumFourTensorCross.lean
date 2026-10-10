import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorSpin
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTensorPair

namespace OAI

/-! Actual inter-block Heisenberg columns in the many-block four-spin code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

def qmaFourTensorPairColumn (i j : Fin n) (p q : Fin 4) (μ : Fin 3) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 2) ℂ :=
  qmaTensorMatrix (fun k => if k = i then qmaFourSpin p μ*qmaFourEncoding
    else if k = j then qmaFourSpin q μ*qmaFourEncoding else qmaFourEncoding)

def qmaFourTensorCross (i j : Fin n) (p q : Fin 4) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  ∑ μ : Fin 3, qmaSiteMatrix i (qmaFourSpin p μ)*qmaSiteMatrix j (qmaFourSpin q μ)

theorem qmaFourTensorCross_column (i j : Fin n) (hij : i ≠ j) (p q : Fin 4) :
    qmaFourTensorCross i j p q*qmaFourTensorEncoding n =
      ∑ μ : Fin 3, qmaFourTensorPairColumn i j p q μ := by
  rw [qmaFourTensorCross,Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Matrix.mul_assoc,qmaFourTensorEncoding,qmaSiteMatrix_tensor,qmaSiteMatrix_tensor,qmaFourTensorPairColumn]
  congr 1
  funext k
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [Ne.symm hij]
    · simp [hki,hkj]

theorem qmaFourTensorPairColumn_orthogonal (i j : Fin n) (p q : Fin 4) (μ : Fin 3) :
    (qmaFourTensorEncoding n).conjTranspose*qmaFourTensorPairColumn i j p q μ = 0 := by
  rw [qmaFourTensorEncoding,qmaFourTensorPairColumn,qmaTensorMatrix_star,qmaTensorMatrix_mul]
  apply qmaTensorMatrix_zero_at _ i
  simp only [ite_true,← Matrix.mul_assoc,qmaFourSpin_orthogonal]

theorem qmaFourTensorPairColumn_excitation (i j : Fin n) (hij : i ≠ j)
    (p q : Fin 4) (μ : Fin 3) :
    qmaFourTensorPenalty n*qmaFourTensorPairColumn i j p q μ =
      (8:ℂ) • qmaFourTensorPairColumn i j p q μ := by
  have h := qmaTensorPenalty_eigen qmaFourPenalty
    (fun k : Fin n => if k = i then qmaFourSpin p μ*qmaFourEncoding
      else if k = j then qmaFourSpin q μ*qmaFourEncoding else qmaFourEncoding)
    (fun k => (if k = i then (4:ℂ) else 0)+(if k = j then (4:ℂ) else 0)) (by
      intro k
      by_cases hki : k = i
      · subst k
        simp only [ite_true,hij,ite_false,add_zero]
        exact qmaFourSpin_excitation p μ
      · by_cases hkj : k = j
        · subst k
          simp only [hki,ite_true,ite_false,zero_add]
          exact qmaFourSpin_excitation q μ
        · simp only [hki,hkj,ite_false,zero_add,zero_smul,qmaFourPenalty_encoding])
  simpa only [qmaFourTensorPenalty,qmaFourTensorPairColumn,Finset.sum_add_distrib,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,show (4:ℂ)+4 = 8 by norm_num] using h

theorem qmaFourTensorCross_orthogonal (i j : Fin n) (hij : i ≠ j) (p q : Fin 4) :
    (qmaFourTensorEncoding n).conjTranspose*(qmaFourTensorCross i j p q*qmaFourTensorEncoding n) = 0 := by
  rw [qmaFourTensorCross_column i j hij,Matrix.mul_sum]
  simp only [qmaFourTensorPairColumn_orthogonal,Finset.sum_const_zero]

theorem qmaFourTensorCross_excitation (i j : Fin n) (hij : i ≠ j) (p q : Fin 4) :
    qmaFourTensorPenalty n*(qmaFourTensorCross i j p q*qmaFourTensorEncoding n) =
      (8:ℂ) • (qmaFourTensorCross i j p q*qmaFourTensorEncoding n) := by
  rw [qmaFourTensorCross_column i j hij,Matrix.mul_sum]
  simp only [qmaFourTensorPairColumn_excitation i j hij,Finset.smul_sum]

theorem qmaFourTensorPairColumn_gram (i j : Fin n)
    (p q r s : Fin 4) (μ ν : Fin 3) :
    (qmaFourTensorPairColumn i j p q μ).conjTranspose*qmaFourTensorPairColumn i j r s ν =
      if μ = ν then qmaPairMatrix i j (qmaFourCorrelation p r) (qmaFourCorrelation q s) else 0 := by
  rw [qmaFourTensorPairColumn,qmaFourTensorPairColumn,qmaTensorMatrix_star,qmaTensorMatrix_mul]
  by_cases hμ : μ = ν
  · subst ν
    rw [ite_eq_left rfl,qmaPairMatrix]
    congr 1
    funext k
    by_cases hki : k = i
    · simp only [hki,ite_true,qmaFourSpin_correlation]
    · by_cases hkj : k = j
      · subst k
        simp only [hki,ite_true,ite_false,qmaFourSpin_correlation]
      · simp only [hki,hkj,ite_false,qmaFourEncoding_gram]
  · rw [ite_eq_right hμ]
    apply qmaTensorMatrix_zero_at _ i
    simp only [ite_true,qmaFourSpin_correlation,hμ,ite_false]

theorem qmaFourTensorCross_gram (i j : Fin n) (hij : i ≠ j) (p q r s : Fin 4) :
    (qmaFourTensorCross i j p q*qmaFourTensorEncoding n).conjTranspose*
      (qmaFourTensorCross i j r s*qmaFourTensorEncoding n) =
        (3:ℂ) • qmaPairMatrix i j (qmaFourCorrelation p r) (qmaFourCorrelation q s) := by
  rw [qmaFourTensorCross_column i j hij,qmaFourTensorCross_column i j hij]
  simp only [Matrix.conjTranspose_sum,Matrix.sum_mul,Matrix.mul_sum,
    qmaFourTensorPairColumn_gram i j,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.sum_const]
  norm_cast

end ContinuumCoulomb

end

end OAI
