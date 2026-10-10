import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTensorPair

namespace OAI

/-! Bilinearity of two-site placements in the finite tensor product. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {Q σ α : Type*} [Fintype Q] [DecidableEq Q] [Fintype σ] [DecidableEq σ] [Fintype α]

omit [Fintype σ] in
theorem qmaSiteMatrix_sum (i : Q) (A : α → Matrix σ σ ℂ) :
    qmaSiteMatrix i (∑ a, A a) = ∑ a, qmaSiteMatrix i (A a) := by
  ext s t
  simp only [qmaSiteMatrix_apply,Matrix.sum_apply,Finset.sum_mul]

theorem qmaPairMatrix_sum_left (i j : Q) (hij : i ≠ j)
    (A : α → Matrix σ σ ℂ) (B : Matrix σ σ ℂ) :
    qmaPairMatrix i j (∑ a, A a) B = ∑ a, qmaPairMatrix i j (A a) B := by
  simp only [qmaPairMatrix_eq_mul _ _ hij,qmaSiteMatrix_sum,Matrix.sum_mul]

theorem qmaPairMatrix_sum_right (i j : Q) (hij : i ≠ j)
    (A : Matrix σ σ ℂ) (B : α → Matrix σ σ ℂ) :
    qmaPairMatrix i j A (∑ a, B a) = ∑ a, qmaPairMatrix i j A (B a) := by
  simp only [qmaPairMatrix_eq_mul _ _ hij,qmaSiteMatrix_sum,Matrix.mul_sum]

omit [Fintype α] in
theorem qmaPairMatrix_one_right (i j : Q) (hij : i ≠ j) (A : Matrix σ σ ℂ) :
    qmaPairMatrix i j A 1 = qmaSiteMatrix i A := by
  rw [qmaPairMatrix_eq_mul i j hij,qmaSiteMatrix_one,Matrix.mul_one]

omit [Fintype α] in
theorem qmaPairMatrix_one_left (i j : Q) (hij : i ≠ j) (A : Matrix σ σ ℂ) :
    qmaPairMatrix i j 1 A = qmaSiteMatrix j A := by
  rw [qmaPairMatrix_eq_mul i j hij,qmaSiteMatrix_one,Matrix.one_mul]

end ContinuumCoulomb

end

end OAI
