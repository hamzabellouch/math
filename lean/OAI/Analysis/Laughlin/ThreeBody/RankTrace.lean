import Mathlib.LinearAlgebra.Matrix.Trace
import OAI.Analysis.Laughlin.ThreeBody.SpinProjectors

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def realOuter {I : Type*} (u v : I → ℝ) : Matrix I I ℝ :=
  fun i j => u i * v j

theorem realOuter_quadratic {I : Type*} [Fintype I] (u v x : I → ℝ) :
    dotProduct x (realOuter u v *ᵥ x) = dotProduct x u * dotProduct x v := by
  simp only [dotProduct,Matrix.mulVec,realOuter]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem trace_outer {I : Type*} [Fintype I] (M : Matrix I I ℝ) (u v : I → ℝ) :
    Matrix.trace (M * realOuter u v) = dotProduct v (M *ᵥ u) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,realOuter,Matrix.mulVec,dotProduct,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem threeSpinProjector_trace (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ) :
    Matrix.trace (threeSpinProjector Q hQ z * M) =
      ∑ n : Fin (coupledWeight Q z.val+1),
        dotProduct (normalizedCoupledDescendant Q z.val hQ (by omega) n.val)
          (M *ᵥ normalizedCoupledDescendant Q z.val hQ (by omega) n.val) := by
  let B := coupledBasisMatrix Q hQ
  have he : Matrix.trace (threeSpinProjector Q hQ z * M) =
      Matrix.trace (coupledSelector Q z * (Bᵀ*M*B)) := by
    change Matrix.trace (B*coupledSelector Q z*Bᵀ*M) = _
    calc
      _ = Matrix.trace ((B*coupledSelector Q z)*(Bᵀ*M)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Bᵀ*M)*(B*coupledSelector Q z)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Bᵀ*M*B)*coupledSelector Q z) := by simp only [Matrix.mul_assoc]
      _ = _ := Matrix.trace_mul_comm _ _
  rw [he]
  unfold coupledSelector
  simp only [Matrix.trace,Matrix.diag,Matrix.diagonal_mul]
  rw [Fintype.sum_sigma]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Matrix.mul_apply,Matrix.transpose_apply,B,coupledBasisMatrix,Matrix.mulVec,dotProduct]
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end Laughlin.Spin

end OAI
