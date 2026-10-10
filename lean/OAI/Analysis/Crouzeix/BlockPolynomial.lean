import Mathlib
import OAI.Analysis.Crouzeix.Vectorization

namespace OAI

/-! Block Polynomial. -/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker TensorProduct

namespace CrouzeixHilbert

def blockPolynomialEval {n m : ℕ} (D : Coeff n) :
    Matrix (Fin m) (Fin m) (Polynomial ℂ) →+*
      Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ where
  toFun M i j := (Polynomial.aeval D (M i.2 j.2)) i.1 j.1
  map_zero' := by ext ⟨i,j⟩ ⟨k,l⟩; simp
  map_one' := by
    ext ⟨i,j⟩ ⟨k,l⟩
    change (Polynomial.aeval D (if j = l then 1 else 0)) i k =
      if (i,j) = (k,l) then 1 else 0
    by_cases h : j = l
    · subst l
      simp only [ite_true, map_one, Matrix.one_apply, Prod.mk.injEq, and_true]
    · simp only [h, ite_false, map_zero, Matrix.zero_apply, Prod.mk.injEq, and_false]
  map_add' M N := by
    ext ⟨i,j⟩ ⟨k,l⟩
    change (Polynomial.aeval D (M j l + N j l)) i k = _ + _
    rw [map_add]
    rfl
  map_mul' M N := by
    ext ⟨i,j⟩ ⟨k,l⟩
    change (Polynomial.aeval D (∑ h, M j h * N h l)) i k =
      ∑ h : Fin n × Fin m, (Polynomial.aeval D (M j h.2)) i h.1 *
        (Polynomial.aeval D (N h.2 l)) h.1 k
    simp only [map_sum, map_mul, Matrix.sum_apply, Matrix.mul_apply,
      Fintype.sum_prod_type]
    rw [Finset.sum_comm]

@[simp] theorem blockPolynomialEval_apply {n m : ℕ} (D : Coeff n)
    (M : Matrix (Fin m) (Fin m) (Polynomial ℂ)) (i k : Fin n) (j l : Fin m) :
    blockPolynomialEval D M (i,j) (k,l) = Polynomial.aeval D (M j l) i k := rfl

theorem blockPolynomialEval_smul_constant {n m : ℕ} (D : Coeff n)
    (p : Polynomial ℂ) (B : Coeff m) :
    blockPolynomialEval D (p • B.map Polynomial.C) = Polynomial.aeval D p ⊗ₖ B := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [blockPolynomialEval_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, map_mul, Polynomial.aeval_C, Matrix.kronecker_apply,
    Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, Matrix.smul_apply]
  exact mul_comm _ _

@[simp] theorem blockPolynomialEval_constant {n m : ℕ} (D : Coeff n) (B : Coeff m) :
    blockPolynomialEval D (B.map Polynomial.C) = 1 ⊗ₖ B := by
  simpa only [one_smul, map_one] using blockPolynomialEval_smul_constant D 1 B

theorem blockPolynomialEval_scalar {n m : ℕ} (D : Coeff n) (p : Polynomial ℂ) :
    blockPolynomialEval (m := m) D (p • 1) = Polynomial.aeval D p ⊗ₖ 1 := by
  have he : (1 : Coeff m).map Polynomial.C = 1 :=
    (Polynomial.C.mapMatrix).map_one
  rw [← he, blockPolynomialEval_smul_constant]

theorem blockPolynomialEval_commute {n m : ℕ} (D : Coeff n) (p : Polynomial ℂ)
    (M : Matrix (Fin m) (Fin m) (Polynomial ℂ)) :
    Commute (Polynomial.aeval D p ⊗ₖ (1 : Coeff m)) (blockPolynomialEval D M) := by
  rw [← blockPolynomialEval_scalar]
  apply Commute.map _ (blockPolynomialEval D)
  show (p • (1 : Matrix (Fin m) (Fin m) (Polynomial ℂ))) * M = M * (p • 1)
  rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

theorem blockPolynomialEval_expansion {n m : ℕ} (D : Coeff n)
    (P : Matrix (Fin m) (Fin m) (Polynomial ℂ)) :
    blockPolynomialEval D P =
      ∑ i, ∑ j, Polynomial.aeval D (P i j) ⊗ₖ Matrix.single i j 1 := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and]

namespace Realization

theorem aeval_reduced_denom_isUnit {A : Type*} [Ring A] [Algebra ℂ A]
    (D : A) (p q : Polynomial ℂ) (hq : IsUnit (Polynomial.aeval D q)) :
    IsUnit (Polynomial.aeval D
      ((algebraMap _ (RatFunc ℂ)) p / (algebraMap _ (RatFunc ℂ)) q).denom) := by
  let r := (algebraMap _ (RatFunc ℂ)) p / (algebraMap _ (RatFunc ℂ)) q
  obtain ⟨b, hb⟩ := RatFunc.denom_div_dvd p q
  have hc := (Commute.all r.denom b).map (Polynomial.aeval D)
  apply (hc.isUnit_mul_iff.mp ?_).1
  rw [← map_mul]
  exact hb ▸ hq

theorem aeval_quotient_cancel {A : Type*} [Ring A] [Algebra ℂ A]
    (D : A) (p q : Polynomial ℂ) (hq0 : q ≠ 0) (hq : IsUnit (Polynomial.aeval D q)) :
    Polynomial.aeval D q *
      (Polynomial.aeval D ((algebraMap _ (RatFunc ℂ)) p / (algebraMap _ (RatFunc ℂ)) q).num *
        Ring.inverse (Polynomial.aeval D ((algebraMap _ (RatFunc ℂ)) p /
          (algebraMap _ (RatFunc ℂ)) q).denom)) = Polynomial.aeval D p := by
  let r := (algebraMap _ (RatFunc ℂ)) p / (algebraMap _ (RatFunc ℂ)) q
  have hd := aeval_reduced_denom_isUnit D p q hq
  have he := congrArg (Polynomial.aeval D)
    ((RatFunc.num_mul_eq_mul_denom_iff hq0).mpr (show r = _ from rfl))
  simp only [map_mul] at he
  change Polynomial.aeval D q * (Polynomial.aeval D r.num * Ring.inverse _) = _
  rw [← mul_assoc, ((Commute.all q r.num).map (Polynomial.aeval D)).eq,
    he, mul_assoc, Ring.mul_inverse_cancel _ hd, mul_one]

theorem map_ringInverse_equiv {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B) (x : A) : e (Ring.inverse x) = Ring.inverse (e x) := by
  by_cases hx : IsUnit x
  · exact map_ringInverse_of_isUnit e.toRingHom hx
  · have hy : ¬ IsUnit (e x) := by
      intro h
      apply hx
      simpa only [RingEquiv.symm_apply_apply] using h.map e.symm
    rw [Ring.inverse_non_unit _ hx, Ring.inverse_non_unit _ hy, map_zero]

end Realization

def rationalBaseMatrix {n : ℕ} (D : Coeff n) (r : RatFunc ℂ) : Coeff n :=
  Polynomial.aeval D r.num * Ring.inverse (Polynomial.aeval D r.denom)

@[simp] theorem rationalEval_matrix {n : ℕ} (D : Coeff n) (r : RatFunc ℂ) :
    rationalEval (Matrix.toEuclideanCLM (𝕜 := ℂ) D) r =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (rationalBaseMatrix D r) := by
  simp only [rationalEval, rationalBaseMatrix, map_mul,
    Polynomial.aeval_algHom_apply]
  congr 1
  exact (Realization.map_ringInverse_equiv
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toRingEquiv _).symm

def blockRationalEval {n m : ℕ} (D : Coeff n) (R : RationalMatrix m) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  ∑ i, ∑ j, rationalBaseMatrix D (R i j) ⊗ₖ Matrix.single i j 1

theorem matrixAmplificationCoordinates_rationalEval {n m : ℕ}
    (D : Coeff n) (R : RationalMatrix m)
    (v : Amplification (EuclideanSpace ℂ (Fin n)) m) :
    matrixAmplificationCoordinates n m
      (matrixRationalEval (Matrix.toEuclideanCLM (𝕜 := ℂ) D) R v) =
        Matrix.toEuclideanCLM (𝕜 := ℂ) (blockRationalEval D R)
          (matrixAmplificationCoordinates n m v) := by
  simp only [matrixRationalEval, blockRationalEval, sum_apply, map_sum,
    rationalEval_matrix, matrixAmplificationCoordinates_tensorOperator]

theorem blockRationalEval_denom_cancel {n m : ℕ} (D : Coeff n)
    (P : Matrix (Fin m) (Fin m) (Polynomial ℂ)) (q : Polynomial ℂ)
    (hq0 : q ≠ 0) (hq : IsUnit (Polynomial.aeval D q)) :
    (Polynomial.aeval D q ⊗ₖ (1 : Coeff m)) *
      blockRationalEval D (fun i j => (algebraMap _ (RatFunc ℂ)) (P i j) /
        (algebraMap _ (RatFunc ℂ)) q) = blockPolynomialEval D P := by
  unfold blockRationalEval
  rw [Finset.mul_sum, blockPolynomialEval_expansion]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.mul_kronecker_mul, one_mul]
  rw [rationalBaseMatrix, Realization.aeval_quotient_cancel D (P i j) q hq0 hq]

end CrouzeixHilbert

end

end OAI
