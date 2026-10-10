import OAI.Combinatorics.PolynomialVacuum.Algebra.PolynomialGenericity

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

 
noncomputable def polynomialSlice {ι : Type*} (c : ι) (Y : ι → ℂ)
    (p : MvPolynomial ι ℂ) : Polynomial ℂ :=
  (optionEquivLeft ℂ {i : ι // i≠c} (rename (Equiv.optionSubtypeNe c).symm p)).map
    (eval (fun i => Y i.val))

theorem polynomialSlice_natDegree {ι : Type*} (c : ι) (Y : ι → ℂ)
    (p : MvPolynomial ι ℂ) : (polynomialSlice c Y p).natDegree ≤ p.degreeOf c := by
  rw [degreeOf_eq_natDegree]
  exact Polynomial.natDegree_map_le

@[simp] theorem polynomialSlice_C {ι : Type*} (c : ι) (Y : ι → ℂ) (z : ℂ) :
    polynomialSlice c Y (C z)=Polynomial.C z := by
  simp [polynomialSlice]

@[simp] theorem polynomialSlice_X {ι : Type*} (c i : ι) (Y : ι → ℂ) :
    polynomialSlice c Y (X i)=if i=c then Polynomial.X else Polynomial.C (Y i) := by
  simp only [polynomialSlice,rename_X,Equiv.optionSubtypeNe_symm_apply]
  split_ifs <;> simp

@[simp] theorem polynomialSlice_add {ι : Type*} (c : ι) (Y : ι → ℂ)
    (p r : MvPolynomial ι ℂ) : polynomialSlice c Y (p+r)=polynomialSlice c Y p+polynomialSlice c Y r := by
  simp [polynomialSlice]

@[simp] theorem polynomialSlice_mul {ι : Type*} (c : ι) (Y : ι → ℂ)
    (p r : MvPolynomial ι ℂ) : polynomialSlice c Y (p*r)=polynomialSlice c Y p*polynomialSlice c Y r := by
  simp [polynomialSlice]

@[simp] theorem eval_polynomialSlice {ι : Type*} (c : ι) (Y : ι → ℂ)
    (p : MvPolynomial ι ℂ) (z : ℂ) :
    (polynomialSlice c Y p).eval z=eval (Function.update Y c z) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp,hr]
  | mul_X p i hp =>
    simp only [polynomialSlice_mul,Polynomial.eval_mul,hp,polynomialSlice_X,map_mul,eval_X]
    split_ifs <;> simp_all

end PolynomialVacuumAlgebra

end OAI
