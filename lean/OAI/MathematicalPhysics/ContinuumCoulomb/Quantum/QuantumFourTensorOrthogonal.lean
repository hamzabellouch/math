import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorCross

namespace OAI

/-! Distinct logical pairs have orthogonal first-excited columns. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

theorem qmaFourSpin_column_adjoint (p : Fin 4) (μ : Fin 3) :
    (qmaFourSpin p μ*qmaFourEncoding).conjTranspose*qmaFourEncoding = 0 := by
  rw [Matrix.conjTranspose_mul,qmaFourSpin_star]
  exact qmaFourSpin_orthogonal p μ

theorem qmaFourTensorPairColumn_unmatched_first (i j k l : Fin n)
    (hik : i ≠ k) (hil : i ≠ l) (p q r s : Fin 4) (μ ν : Fin 3) :
    (qmaFourTensorPairColumn i j p q μ).conjTranspose*
      qmaFourTensorPairColumn k l r s ν = 0 := by
  rw [qmaFourTensorPairColumn,qmaFourTensorPairColumn,qmaTensorMatrix_star,qmaTensorMatrix_mul]
  apply qmaTensorMatrix_zero_at _ i
  simp only [ite_true,hik,hil,ite_false,qmaFourSpin_column_adjoint]

theorem qmaFourTensorPairColumn_unmatched_second (i j k l : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hjl : j ≠ l) (p q r s : Fin 4) (μ ν : Fin 3) :
    (qmaFourTensorPairColumn i j p q μ).conjTranspose*
      qmaFourTensorPairColumn k l r s ν = 0 := by
  rw [qmaFourTensorPairColumn,qmaFourTensorPairColumn,qmaTensorMatrix_star,qmaTensorMatrix_mul]
  apply qmaTensorMatrix_zero_at _ j
  simp only [Ne.symm hij,ite_false,ite_true,hjk,hjl,qmaFourSpin_column_adjoint]

theorem qmaFourTensorPairColumn_distinct (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hne : ({i,j} : Finset (Fin n)) ≠ {k,l}) (p q r s : Fin 4) (μ ν : Fin 3) :
    (qmaFourTensorPairColumn i j p q μ).conjTranspose*
      qmaFourTensorPairColumn k l r s ν = 0 := by
  by_cases hi : i ∈ ({k,l} : Finset (Fin n))
  · by_cases hj : j ∈ ({k,l} : Finset (Fin n))
    · exfalso
      apply hne
      have hsub : ({i,j} : Finset (Fin n)) ⊆ {k,l} := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hi
        · simpa only [Finset.mem_singleton.mp hx] using hj
      exact Finset.eq_of_subset_of_card_le hsub (by simp [hij,hkl])
    · have hj' : j ≠ k ∧ j ≠ l := by simpa using hj
      exact qmaFourTensorPairColumn_unmatched_second i j k l hij hj'.1 hj'.2 p q r s μ ν
  · have hi' : i ≠ k ∧ i ≠ l := by simpa using hi
    exact qmaFourTensorPairColumn_unmatched_first i j k l hi'.1 hi'.2 p q r s μ ν

theorem qmaFourTensorCross_distinct (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hne : ({i,j} : Finset (Fin n)) ≠ {k,l}) (p q r s : Fin 4) :
    (qmaFourTensorCross i j p q*qmaFourTensorEncoding n).conjTranspose*
      (qmaFourTensorCross k l r s*qmaFourTensorEncoding n) = 0 := by
  rw [qmaFourTensorCross_column i j hij,qmaFourTensorCross_column k l hkl]
  simp only [Matrix.conjTranspose_sum,Matrix.sum_mul,Matrix.mul_sum,
    qmaFourTensorPairColumn_distinct i j k l hij hkl hne,Finset.sum_const_zero]

end ContinuumCoulomb

end

end OAI
