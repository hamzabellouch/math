import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Finset Classical
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.Localization
open Matrix Finset
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma sum_fin_fun_succ [DecidableEq ι] (n : ℕ) (F : (Fin (n+1) → ι) → ℂ) :
    (∑ v : Fin (n+1) → ι,F v) = ∑ a : ι,∑ v : Fin n → ι,F (Fin.cons a v) := by
  calc
    _ = ∑ av : ι × (Fin n → ι),F (Fin.cons av.1 av.2) := by
      symm
      exact Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => ι)) _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_prod_type _

def matrixWalkProduct (M : Matrix ι ι ℂ) (m : ℕ) (v : Fin (m+1) → ι) : ℂ :=
  ∏ i : Fin m,M (v i.castSucc) (v i.succ)

omit [Fintype ι] [DecidableEq ι] in
lemma matrixWalkProduct_cons [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (m : ℕ) (a : ι) (v : Fin (m+1) → ι) :
    matrixWalkProduct M (m+1) (Fin.cons a v)=M a (v 0)*matrixWalkProduct M m v := by
  unfold matrixWalkProduct
  rw [Fin.prod_univ_succ]
  simp only [Fin.castSucc_zero,Fin.cons_zero,Fin.succ_zero_eq_one,Fin.cons_one,
    Fin.castSucc_succ,Fin.cons_succ]

theorem matrix_pow_walks (M : Matrix ι ι ℂ) (m : ℕ) (x y : ι) :
    (M^m) x y=∑ v : Fin (m+1) → ι,
      if v 0=x then if v (Fin.last m)=y then matrixWalkProduct M m v else 0 else 0 := by
  induction m generalizing x y with
  | zero =>
    rw [sum_fin_fun_succ]
    simp [matrixWalkProduct,Matrix.one_apply]
  | succ m ih =>
    rw [_root_.pow_succ',Matrix.mul_apply]
    simp_rw [ih,mul_sum]
    rw [sum_comm,sum_fin_fun_succ (m+1)]
    simp only [Fin.cons_zero,show Fin.last (m+1)=(Fin.last m).succ from rfl,
      Fin.cons_succ,matrixWalkProduct_cons]
    simp only [mul_ite,mul_zero]
    conv_rhs => rw [sum_comm]
    simp

theorem matrix_trace_walks (M : Matrix ι ι ℂ) (m : ℕ) :
    (M^m).trace=∑ v : Fin (m+1) → ι,
      if v (Fin.last m)=v 0 then matrixWalkProduct M m v else 0 := by
  simp only [Matrix.trace,Matrix.diag,matrix_pow_walks]
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  simp

theorem matrix_gram_trace_expansion (M : Matrix ι ι ℂ) (m : ℕ) :
    ((M.conjTranspose*M)^m).trace=
      ∑ v : Fin (m+1) → ι,if v (Fin.last m)=v 0 then
        ∑ x : Fin m → ι,∏ j : Fin m,star (M (x j) (v j.castSucc))*M (x j) (v j.succ)
      else 0 := by
  rw [matrix_trace_walks]
  apply sum_congr rfl
  intro v hv
  split_ifs
  · simp only [matrixWalkProduct,Matrix.mul_apply,Matrix.conjTranspose_apply]
    exact Fintype.prod_sum _
  · rfl

end
end OrdinaryCorrelations.Localization

end

end OAI
