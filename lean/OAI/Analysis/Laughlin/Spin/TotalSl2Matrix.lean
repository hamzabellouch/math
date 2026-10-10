import Mathlib.Tactic.Abel
import OAI.Analysis.Laughlin.Spin.Sl2Matrix
import OAI.Analysis.Laughlin.Spin.TripleLadderIntertwining
import OAI.Analysis.Laughlin.Spin.WeightSlice

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

noncomputable def totalWeight (A B : ℕ) : Matrix (SpinIndex A B) (SpinIndex A B) ℝ :=
  weightMatrix A ⊗ₖ (1 : Matrix (Fin (B+1)) (Fin (B+1)) ℝ) +
    (1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ weightMatrix B

theorem totalRaise_transpose_kronecker (A B : ℕ) :
    (totalRaise A B)ᵀ = (raiseMatrix A)ᵀ ⊗ₖ (1 : Matrix (Fin (B+1)) (Fin (B+1)) ℝ) +
      (1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ (raiseMatrix B)ᵀ := by
  ext i j
  simp [totalRaise,Matrix.kroneckerMap,Matrix.transpose_apply,Matrix.one_apply,eq_comm]

theorem total_raise_lower_commutator (A B : ℕ) :
    totalRaise A B * (totalRaise A B)ᵀ =
      (totalRaise A B)ᵀ * totalRaise A B + totalWeight A B := by
  have ha : raiseMatrix A*(raiseMatrix A)ᵀ = (raiseMatrix A)ᵀ*raiseMatrix A+weightMatrix A := by
    calc
      _ = (raiseMatrix A*(raiseMatrix A)ᵀ - (raiseMatrix A)ᵀ*raiseMatrix A) +
        (raiseMatrix A)ᵀ*raiseMatrix A := by abel
      _ = _ := by rw [raise_lower_commutator A]; abel
  have hb : raiseMatrix B*(raiseMatrix B)ᵀ = (raiseMatrix B)ᵀ*raiseMatrix B+weightMatrix B := by
    calc
      _ = (raiseMatrix B*(raiseMatrix B)ᵀ - (raiseMatrix B)ᵀ*raiseMatrix B) +
        (raiseMatrix B)ᵀ*raiseMatrix B := by abel
      _ = _ := by rw [raise_lower_commutator B]; abel
  rw [totalRaise_transpose_kronecker,totalRaise_kronecker]
  unfold totalWeight
  simp only [Matrix.add_mul,Matrix.mul_add,← Matrix.mul_kronecker_mul,
    Matrix.one_mul,Matrix.mul_one,ha,hb,Matrix.add_kronecker,Matrix.kronecker_add]
  abel

theorem total_weight_lower_commutator (A B : ℕ) :
    totalWeight A B * (totalRaise A B)ᵀ =
      (totalRaise A B)ᵀ * totalWeight A B - (2 : ℝ) • (totalRaise A B)ᵀ := by
  have ha : weightMatrix A*(raiseMatrix A)ᵀ =
      (raiseMatrix A)ᵀ*weightMatrix A+(-2 : ℝ) • (raiseMatrix A)ᵀ := by
    simpa only [sub_eq_add_neg,neg_smul] using weight_lower_commutator A
  have hb : weightMatrix B*(raiseMatrix B)ᵀ =
      (raiseMatrix B)ᵀ*weightMatrix B+(-2 : ℝ) • (raiseMatrix B)ᵀ := by
    simpa only [sub_eq_add_neg,neg_smul] using weight_lower_commutator B
  rw [totalRaise_transpose_kronecker]
  unfold totalWeight
  simp only [Matrix.add_mul,Matrix.mul_add,← Matrix.mul_kronecker_mul,
    Matrix.one_mul,Matrix.mul_one,ha,hb,Matrix.add_kronecker,Matrix.kronecker_add,
    smul_add,neg_smul,sub_eq_add_neg]
  ext i j
  simp only [Matrix.add_apply,Matrix.neg_apply,Matrix.smul_apply,Matrix.kroneckerMap,
    Matrix.of_apply,smul_eq_mul]
  ring

theorem totalWeight_diagonal (A B : ℕ) :
    totalWeight A B = Matrix.diagonal (fun i : SpinIndex A B =>
      (A : ℝ)+B-2*((i.1.val : ℝ)+i.2.val)) := by
  ext i j
  by_cases h₁ : i.1=j.1 <;> by_cases h₂ : i.2=j.2 <;>
    simp [totalWeight,weightMatrix,Matrix.kroneckerMap,
      Matrix.one_apply,Matrix.diagonal_apply,Prod.ext_iff,h₁,h₂]
  ring

end Laughlin.Spin

end OAI
