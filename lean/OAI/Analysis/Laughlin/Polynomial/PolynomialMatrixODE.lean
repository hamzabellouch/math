import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul

namespace OAI

namespace Laughlin.Rotation
open Polynomial
open scoped BigOperators Matrix

noncomputable def polynomialMatrixDerivative {ι κ : Type*}
    (P : Matrix ι κ (Polynomial ℂ)) : Matrix ι κ (Polynomial ℂ) := fun i j => (P i j).derivative
noncomputable def polynomialMatrixCoeff {ι κ : Type*}
    (P : Matrix ι κ (Polynomial ℂ)) (n : ℕ) : Matrix ι κ ℂ := fun i j => (P i j).coeff n

theorem polynomialMatrixDerivative_coeff {ι κ : Type*} (P : Matrix ι κ (Polynomial ℂ)) (n : ℕ) :
    polynomialMatrixCoeff (polynomialMatrixDerivative P) n =
      (n+1 : ℂ) • polynomialMatrixCoeff P (n+1) := by
  ext i j
  simp [polynomialMatrixCoeff,polynomialMatrixDerivative,coeff_derivative,mul_comm]

theorem polynomialMatrixCoeff_mul_constant {ι κ τ : Type*} [Fintype κ]
    (P : Matrix ι κ (Polynomial ℂ)) (G : Matrix κ τ ℂ) (n : ℕ) :
    polynomialMatrixCoeff (P * G.map C) n = polynomialMatrixCoeff P n * G := by
  ext i j
  simp [polynomialMatrixCoeff,Matrix.mul_apply,coeff_mul_C]

theorem polynomialMatrixCoeff_constant_mul {ι κ τ : Type*} [Fintype κ]
    (G : Matrix ι κ ℂ) (P : Matrix κ τ (Polynomial ℂ)) (n : ℕ) :
    polynomialMatrixCoeff (G.map C * P) n = G * polynomialMatrixCoeff P n := by
  ext i j
  simp [polynomialMatrixCoeff,Matrix.mul_apply,coeff_C_mul]

theorem polynomialMatrixDerivative_mul {ι κ τ : Type*} [Fintype κ]
    (P : Matrix ι κ (Polynomial ℂ)) (Q : Matrix κ τ (Polynomial ℂ)) :
    polynomialMatrixDerivative (P*Q) = polynomialMatrixDerivative P*Q+P*polynomialMatrixDerivative Q := by
  ext i j
  simp [polynomialMatrixDerivative,Matrix.mul_apply,derivative_mul,Finset.sum_add_distrib]

theorem polynomialMatrixDerivative_constant {ι κ : Type*} (G : Matrix ι κ ℂ) :
    polynomialMatrixDerivative (G.map C)=0 := by
  ext i j
  simp [polynomialMatrixDerivative]

theorem polynomialMatrixDerivative_sub {ι κ : Type*}
    (P Q : Matrix ι κ (Polynomial ℂ)) :
    polynomialMatrixDerivative (P-Q)=polynomialMatrixDerivative P-polynomialMatrixDerivative Q := by
  ext i j
  simp [polynomialMatrixDerivative]

theorem polynomialMatrixCoeff_sub {ι κ : Type*}
    (P Q : Matrix ι κ (Polynomial ℂ)) (n : ℕ) :
    polynomialMatrixCoeff (P-Q) n=polynomialMatrixCoeff P n-polynomialMatrixCoeff Q n := by
  ext i j
  simp [polynomialMatrixCoeff]

theorem polynomialMatrix_zero_of_derivative_right {ι κ : Type*} [Fintype κ]
    (P : Matrix ι κ (Polynomial ℂ)) (G : Matrix κ κ ℂ)
    (hd : polynomialMatrixDerivative P=P*G.map C)
    (h0 : polynomialMatrixCoeff P 0=0) : P=0 := by
  have hc : ∀ n, polynomialMatrixCoeff P n=0 := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      have h := congrArg (fun M => polynomialMatrixCoeff M n) hd
      rw [polynomialMatrixDerivative_coeff,polynomialMatrixCoeff_mul_constant,ih,Matrix.zero_mul] at h
      exact (smul_eq_zero.mp h).resolve_left (by exact_mod_cast Nat.succ_ne_zero n)
  ext i j n
  exact congrFun (congrFun (hc n) i) j

theorem polynomialMatrix_intertwining {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι ι (Polynomial ℂ)) (V : Matrix κ κ (Polynomial ℂ))
    (G : Matrix ι ι ℂ) (H : Matrix κ κ ℂ) (W : Matrix ι κ ℂ)
    (hU : polynomialMatrixDerivative U=U*G.map C)
    (hV : polynomialMatrixDerivative V=V*H.map C)
    (hU0 : polynomialMatrixCoeff U 0=1) (hV0 : polynomialMatrixCoeff V 0=1)
    (hW : G*W=W*H) : U*W.map C=W.map C*V := by
  have hWC : G.map C*W.map C=W.map C*H.map C := by
    simpa only [Matrix.map_mul] using congrArg (fun M => M.map C) hW
  have hd : polynomialMatrixDerivative (U*W.map C-W.map C*V) =
      (U*W.map C-W.map C*V)*H.map C := by
    rw [polynomialMatrixDerivative_sub,polynomialMatrixDerivative_mul,polynomialMatrixDerivative_mul,
      polynomialMatrixDerivative_constant,hU,hV,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,
      Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
    rw [hWC]
  have h0 : polynomialMatrixCoeff (U*W.map C-W.map C*V) 0=0 := by
    rw [polynomialMatrixCoeff_sub,polynomialMatrixCoeff_mul_constant,
      polynomialMatrixCoeff_constant_mul,hU0,hV0,Matrix.one_mul,Matrix.mul_one,sub_self]
  exact sub_eq_zero.mp (polynomialMatrix_zero_of_derivative_right _ H hd h0)

end Laughlin.Rotation

end OAI
