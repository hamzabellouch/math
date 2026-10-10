import Mathlib.LinearAlgebra.Matrix.Kronecker
import OAI.Analysis.Laughlin.Pair.LadderIntertwining

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

abbrev Orbital (Q : ℕ) := Fin (Q+1)
abbrev TripleIndex (Q : ℕ) := (Orbital Q × Orbital Q) × Orbital Q
abbrev PairOrbitalIndex (Q : ℕ) := Fin ((2*Q-2)+1) × Orbital Q

theorem totalRaise_kronecker (A B : ℕ) :
    totalRaise A B = raiseMatrix A ⊗ₖ (1 : Matrix (Fin (B+1)) (Fin (B+1)) ℝ) +
      (1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ raiseMatrix B := by
  rfl

noncomputable def tripleInclusion (Q : ℕ) : Matrix (TripleIndex Q) (PairOrbitalIndex Q) ℝ :=
  pairInclusion Q ⊗ₖ (1 : Matrix (Orbital Q) (Orbital Q) ℝ)

noncomputable def tripleRaise (Q : ℕ) : Matrix (TripleIndex Q) (TripleIndex Q) ℝ :=
  totalRaise Q Q ⊗ₖ (1 : Matrix (Orbital Q) (Orbital Q) ℝ) +
    (1 : Matrix (Orbital Q × Orbital Q) (Orbital Q × Orbital Q) ℝ) ⊗ₖ raiseMatrix Q

theorem tripleInclusion_raising (Q : ℕ) (hQ : 0 < Q) :
    tripleRaise Q * tripleInclusion Q = tripleInclusion Q * totalRaise (2*Q-2) Q := by
  rw [totalRaise_kronecker]
  unfold tripleRaise tripleInclusion
  simp only [Matrix.add_mul,Matrix.mul_add,← Matrix.mul_kronecker_mul,
    Matrix.mul_one,Matrix.one_mul,pairInclusion_raising Q hQ]

theorem tripleInclusion_transpose (Q : ℕ) :
    (tripleInclusion Q)ᵀ = (pairInclusion Q)ᵀ ⊗ₖ (1 : Matrix (Orbital Q) (Orbital Q) ℝ) := by
  ext i j
  simp [tripleInclusion,Matrix.kroneckerMap,Matrix.transpose_apply,Matrix.one_apply,eq_comm]

theorem tripleInclusion_transpose_raising (Q : ℕ) (hQ : 0 < Q) :
    (tripleInclusion Q)ᵀ * tripleRaise Q = totalRaise (2*Q-2) Q * (tripleInclusion Q)ᵀ := by
  rw [tripleInclusion_transpose,totalRaise_kronecker]
  unfold tripleRaise
  simp only [Matrix.add_mul,Matrix.mul_add,← Matrix.mul_kronecker_mul,
    Matrix.mul_one,Matrix.one_mul,pairInclusion_transpose_raising Q hQ]

theorem tripleInclusion_isometry (Q : ℕ) (hQ : 2 ≤ Q) :
    (tripleInclusion Q)ᵀ * tripleInclusion Q = 1 := by
  rw [tripleInclusion_transpose]
  unfold tripleInclusion
  rw [← Matrix.mul_kronecker_mul,pairInclusion_isometry Q hQ,Matrix.mul_one,
    Matrix.one_kronecker_one]

def swap23 {Q : ℕ} (i : TripleIndex Q) : TripleIndex Q := ((i.1.1,i.2),i.1.2)

@[simp] theorem swap23_involutive {Q : ℕ} (i : TripleIndex Q) : swap23 (swap23 i) = i := by
  rcases i with ⟨⟨i,j⟩,k⟩; rfl

noncomputable def swap23Matrix (Q : ℕ) : Matrix (TripleIndex Q) (TripleIndex Q) ℝ :=
  fun i j => if swap23 i=j then 1 else 0

theorem swap23Matrix_mul (Q : ℕ) (M : Matrix (TripleIndex Q) (TripleIndex Q) ℝ)
    (i j : TripleIndex Q) : (swap23Matrix Q * M) i j = M (swap23 i) j := by
  simp [Matrix.mul_apply,swap23Matrix]

theorem mul_swap23Matrix (Q : ℕ) (M : Matrix (TripleIndex Q) (TripleIndex Q) ℝ)
    (i j : TripleIndex Q) : (M * swap23Matrix Q) i j = M i (swap23 j) := by
  have he (k : TripleIndex Q) : swap23 k=j ↔ k=swap23 j := by
    constructor
    · intro h; simpa using congrArg swap23 h
    · intro h; rw [h,swap23_involutive]
  simp [Matrix.mul_apply,swap23Matrix,he]

theorem swap23_raising (Q : ℕ) : swap23Matrix Q * tripleRaise Q = tripleRaise Q * swap23Matrix Q := by
  ext a b
  rw [swap23Matrix_mul,mul_swap23Matrix]
  rcases a with ⟨⟨i,j⟩,k⟩
  rcases b with ⟨⟨l,m⟩,n⟩
  simp only [tripleRaise,totalRaise,Matrix.add_apply,Matrix.kroneckerMap,
    Matrix.one_apply,Matrix.of_apply,swap23,Prod.mk.injEq]
  split_ifs <;> simp_all
  ring

end Laughlin.Spin

end OAI
