import OAI.Analysis.Laughlin.Asymptotics.UpperSpinCurve
import OAI.Analysis.Laughlin.Polynomial.PolynomialMatrixODE
import OAI.Analysis.Laughlin.Spin.TotalSl2Matrix

namespace OAI

namespace Laughlin.Rotation
open Polynomial
open scoped BigOperators Matrix Kronecker

noncomputable def spinRaiseComplex (Q : ℕ) := (Spin.raiseMatrix Q).map Complex.ofReal
noncomputable def totalRaiseComplex (A B : ℕ) := (Spin.totalRaise A B).map Complex.ofReal

theorem upperSpinCurve_derivative (Q : ℕ) :
    polynomialMatrixDerivative (upperSpinCurve Q) = upperSpinCurve Q * (spinRaiseComplex Q).map C := by
  funext p q
  induction q using Fin.cases with
  | zero =>
    change (upperSpinCurve Q p 0).derivative = _
    rw [upperSpinCurve_derivative_zero]
    simp [Matrix.mul_apply,spinRaiseComplex,Spin.raiseMatrix]
  | succ q =>
    change (upperSpinCurve Q p q.succ).derivative = _
    rw [upperSpinCurve_derivative_succ,Matrix.mul_apply]
    have he (r : Fin (Q+1)) : r.val+1=q.succ.val ↔ r=q.castSucc := by
      simp [Fin.ext_iff]
    simp only [spinRaiseComplex,Matrix.map_apply,Spin.raiseMatrix,he,apply_ite,
      Complex.ofReal_zero,map_zero,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
      Fin.val_castSucc]

theorem upperSpinCurve_initial (Q : ℕ) : polynomialMatrixCoeff (upperSpinCurve Q) 0=1 := by
  ext p q
  exact upperSpinCurve_zero Q p q

theorem polynomialMatrixDerivative_kronecker {ι κ τ υ : Type*}
    (P : Matrix ι κ (Polynomial ℂ)) (Q : Matrix τ υ (Polynomial ℂ)) :
    polynomialMatrixDerivative (P ⊗ₖ Q)=
      polynomialMatrixDerivative P ⊗ₖ Q+P ⊗ₖ polynomialMatrixDerivative Q := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [polynomialMatrixDerivative,Matrix.kroneckerMap,derivative_mul]

theorem polynomialMatrixCoeff_kronecker_zero {ι κ τ υ : Type*}
    (P : Matrix ι κ (Polynomial ℂ)) (Q : Matrix τ υ (Polynomial ℂ)) :
    polynomialMatrixCoeff (P ⊗ₖ Q) 0=polynomialMatrixCoeff P 0 ⊗ₖ polynomialMatrixCoeff Q 0 := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [polynomialMatrixCoeff,Matrix.kroneckerMap]

theorem totalRaiseComplex_polynomial (A B : ℕ) :
    (totalRaiseComplex A B).map C =
      (spinRaiseComplex A).map C ⊗ₖ (1 : Matrix (Fin (B+1)) (Fin (B+1)) (Polynomial ℂ)) +
      (1 : Matrix (Fin (A+1)) (Fin (A+1)) (Polynomial ℂ)) ⊗ₖ (spinRaiseComplex B).map C := by
  ext ⟨i,j⟩ ⟨k,l⟩ : 2
  by_cases hik : i=k <;> by_cases hjl : j=l <;>
    simp [totalRaiseComplex,spinRaiseComplex,Spin.totalRaise,Matrix.kroneckerMap,
      Matrix.one_apply,hik,hjl]

theorem upperSpinTensor_derivative (A B : ℕ) :
    polynomialMatrixDerivative (upperSpinCurve A ⊗ₖ upperSpinCurve B) =
      (upperSpinCurve A ⊗ₖ upperSpinCurve B)*(totalRaiseComplex A B).map C := by
  rw [polynomialMatrixDerivative_kronecker,upperSpinCurve_derivative,upperSpinCurve_derivative,
    totalRaiseComplex_polynomial,Matrix.mul_add]
  simp only [← Matrix.mul_kronecker_mul,Matrix.mul_one]

theorem upperSpinTensor_initial (A B : ℕ) :
    polynomialMatrixCoeff (upperSpinCurve A ⊗ₖ upperSpinCurve B) 0=1 := by
  rw [polynomialMatrixCoeff_kronecker_zero,upperSpinCurve_initial,upperSpinCurve_initial,
    Matrix.one_kronecker_one]

theorem raising_intertwiner_upper (A B J : ℕ)
    (W : Matrix (Fin (A+1) × Fin (B+1)) (Fin (J+1)) ℂ)
    (hW : totalRaiseComplex A B*W=W*spinRaiseComplex J) (c : ℂ) :
    (generalSpinMatrix A (Matrix.transvection (0 : Fin 2) 1 c) ⊗ₖ
      generalSpinMatrix B (Matrix.transvection (0 : Fin 2) 1 c))*W =
        W*generalSpinMatrix J (Matrix.transvection (0 : Fin 2) 1 c) := by
  have h := polynomialMatrix_intertwining (upperSpinCurve A ⊗ₖ upperSpinCurve B)
    (upperSpinCurve J) (totalRaiseComplex A B) (spinRaiseComplex J) W
    (upperSpinTensor_derivative A B) (upperSpinCurve_derivative J)
    (upperSpinTensor_initial A B) (upperSpinCurve_initial J) hW
  ext i j
  have he := congrArg (fun M => (M i j).eval c) h
  simpa [Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap,eval_finsetSum,eval_mul,upperSpinCurve_eval] using he

theorem lowering_intertwiner_lower (A B J : ℕ)
    (W : Matrix (Fin (A+1) × Fin (B+1)) (Fin (J+1)) ℂ)
    (hW : (totalRaiseComplex A B)ᵀ*W=W*(spinRaiseComplex J)ᵀ) (c : ℂ) :
    (generalSpinMatrix A (Matrix.transvection (1 : Fin 2) 0 c) ⊗ₖ
      generalSpinMatrix B (Matrix.transvection (1 : Fin 2) 0 c))*W =
        W*generalSpinMatrix J (Matrix.transvection (1 : Fin 2) 0 c) := by
  have ht : spinRaiseComplex J*Wᵀ=Wᵀ*totalRaiseComplex A B := by
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose] using congrArg Matrix.transpose hW.symm
  have h := polynomialMatrix_intertwining (upperSpinCurve J)
    (upperSpinCurve A ⊗ₖ upperSpinCurve B) (spinRaiseComplex J) (totalRaiseComplex A B) Wᵀ
    (upperSpinCurve_derivative J) (upperSpinTensor_derivative A B)
    (upperSpinCurve_initial J) (upperSpinTensor_initial A B) ht
  have he : W*(generalSpinMatrix J (Matrix.transvection (0 : Fin 2) 1 c))ᵀ =
      (generalSpinMatrix A (Matrix.transvection (0 : Fin 2) 1 c) ⊗ₖ
      generalSpinMatrix B (Matrix.transvection (0 : Fin 2) 1 c))ᵀ*W := by
    have hh := congrArg Matrix.transpose h
    ext i j
    have hh' := congrArg (fun M => (M i j).eval c) hh
    simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.kronecker,Matrix.kroneckerMap,
      eval_finsetSum,eval_mul,upperSpinCurve_eval,mul_comm] using hh'
  have hf : (Matrix.transvection (0 : Fin 2) 1 c)ᵀ=Matrix.transvection 1 0 c := by
    ext i j
    simp [Matrix.transvection,Matrix.transpose_apply,Matrix.single,Matrix.one_apply,eq_comm,and_comm]
  change W*(generalSpinMatrix J (Matrix.transvection (0 : Fin 2) 1 c))ᵀ =
    ((generalSpinMatrix A (Matrix.transvection (0 : Fin 2) 1 c))ᵀ ⊗ₖ
     (generalSpinMatrix B (Matrix.transvection (0 : Fin 2) 1 c))ᵀ)*W at he
  rw [← generalSpinMatrix_transpose,← generalSpinMatrix_transpose,
    ← generalSpinMatrix_transpose,hf] at he
  exact he.symm

end Laughlin.Rotation

end OAI
