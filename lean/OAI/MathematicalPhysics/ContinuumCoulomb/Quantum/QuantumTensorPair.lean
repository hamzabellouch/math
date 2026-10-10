import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTensorAction

namespace OAI

/-! Two-block tensor placements and their exact algebra. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {Q σ : Type*} [Fintype Q] [DecidableEq Q] [Fintype σ] [DecidableEq σ]

def qmaPairMatrix (i j : Q) (A B : Matrix σ σ ℂ) : Matrix (Q → σ) (Q → σ) ℂ :=
  qmaTensorMatrix (fun k => if k = i then A else if k = j then B else 1)

theorem qmaPairMatrix_eq_mul (i j : Q) (hij : i ≠ j) (A B : Matrix σ σ ℂ) :
    qmaPairMatrix i j A B = qmaSiteMatrix i A*qmaSiteMatrix j B := by
  rw [qmaPairMatrix,qmaSiteMatrix,qmaSiteMatrix,qmaTensorMatrix_mul]
  congr 1
  funext k
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [Ne.symm hij]
    · simp [hki,hkj]

omit [Fintype σ] in
theorem qmaPairMatrix_zero_left (i j : Q) (B : Matrix σ σ ℂ) : qmaPairMatrix i j 0 B = 0 := by
  apply qmaTensorMatrix_zero_at _ i
  simp

theorem qmaPairMatrix_add_left (i j : Q) (hij : i ≠ j) (A B C : Matrix σ σ ℂ) :
    qmaPairMatrix i j (A+B) C = qmaPairMatrix i j A C+qmaPairMatrix i j B C := by
  simp only [qmaPairMatrix_eq_mul _ _ hij,qmaSiteMatrix_add,Matrix.add_mul]

theorem qmaPairMatrix_add_right (i j : Q) (hij : i ≠ j) (A B C : Matrix σ σ ℂ) :
    qmaPairMatrix i j A (B+C) = qmaPairMatrix i j A B+qmaPairMatrix i j A C := by
  simp only [qmaPairMatrix_eq_mul _ _ hij,qmaSiteMatrix_add,Matrix.mul_add]

theorem qmaPairMatrix_smul_left (i j : Q) (hij : i ≠ j) (r : ℂ) (A B : Matrix σ σ ℂ) :
    qmaPairMatrix i j (r • A) B = r • qmaPairMatrix i j A B := by
  simp only [qmaPairMatrix_eq_mul _ _ hij,qmaSiteMatrix_smul,Matrix.smul_mul]

theorem qmaPairMatrix_smul_right (i j : Q) (hij : i ≠ j) (r : ℂ) (A B : Matrix σ σ ℂ) :
    qmaPairMatrix i j A (r • B) = r • qmaPairMatrix i j A B := by
  simp only [qmaPairMatrix_eq_mul _ _ hij,qmaSiteMatrix_smul,Matrix.mul_smul]

end ContinuumCoulomb

end

end OAI
