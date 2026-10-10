import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ForwardHermitianForm
import Mathlib.Algebra.Polynomial.Degree.Lemmas

namespace OAI

/-! # Polynomial structure of the finite forward matrix

Only the constant coefficient depends on the spectral shift. The leading
matrix is computed for every truncation depth, independently of parameters.
-/

open Polynomial Matrix

namespace DefocusingNLS

noncomputable def boundaryLinear (a : ℂ) : Polynomial ℂ := C a + C Complex.I * X

noncomputable def boundaryForwardStep (M : ℝ) (s a : ℂ) :
    Matrix (Fin 2) (Fin 2) (Polynomial ℂ) :=
  !![boundaryLinear a, C s; -boundaryLinear a, boundaryLinear a - C (M : ℂ) - C s]

noncomputable def boundaryForwardProduct (M : ℝ) (s : ℂ) (a : ℕ → ℂ) :
    ℕ → Matrix (Fin 2) (Fin 2) (Polynomial ℂ)
  | 0 => 1
  | K + 1 => boundaryForwardStep M s (a K) * boundaryForwardProduct M s a K

theorem boundaryLinear_degree (a : ℂ) : (boundaryLinear a).natDegree ≤ 1 := by
  apply natDegree_add_le_of_degree_le
  · simp
  · exact (natDegree_C_mul_le (Complex.I : ℂ) (X : Polynomial ℂ)).trans (by simp)

theorem boundaryForwardStep_degree (M : ℝ) (s a : ℂ) (i j : Fin 2) :
    (boundaryForwardStep M s a i j).natDegree ≤ 1 := by
  fin_cases i <;> fin_cases j
  · exact boundaryLinear_degree _
  · change (C s).natDegree ≤ 1
    simp
  · change (-boundaryLinear a).natDegree ≤ 1
    simpa only [natDegree_neg] using boundaryLinear_degree a
  · change (boundaryLinear a - C (M : ℂ) - C s).natDegree ≤ 1
    apply (natDegree_sub_le _ _).trans
    apply max_le _ (by simp)
    exact (natDegree_sub_le _ _).trans (max_le (boundaryLinear_degree _) (by simp))

theorem boundaryForwardProduct_degree (M : ℝ) (s : ℂ) (a : ℕ → ℂ)
    (K : ℕ) (i j : Fin 2) : (boundaryForwardProduct M s a K i j).natDegree ≤ K := by
  induction K generalizing i j with
  | zero => fin_cases i <;> fin_cases j <;> simp [boundaryForwardProduct]
  | succ K ih =>
    change (∑ k, boundaryForwardStep M s (a K) i k *
      boundaryForwardProduct M s a K k j).natDegree ≤ K + 1
    rw [Fin.sum_univ_two]
    apply natDegree_add_le_of_degree_le
    · exact (natDegree_mul_le.trans (add_le_add (boundaryForwardStep_degree ..) (ih ..))).trans
        (by omega)
    · exact (natDegree_mul_le.trans (add_le_add (boundaryForwardStep_degree ..) (ih ..))).trans
        (by omega)

theorem boundaryLinear_mul_top (a : ℂ) (p : Polynomial ℂ) (K : ℕ)
    (hp : p.natDegree ≤ K) :
    (boundaryLinear a * p).coeff (K + 1) = Complex.I * p.coeff K := by
  have hz : p.coeff (K + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  simp [boundaryLinear, add_mul, mul_assoc, coeff_X_mul, hz]

theorem boundaryForwardProduct_top (M : ℝ) (s : ℂ) (a : ℕ → ℂ) (K : ℕ) :
    (boundaryForwardProduct M s a K 0 0).coeff K = Complex.I ^ K ∧
    (boundaryForwardProduct M s a K 0 1).coeff K = 0 ∧
    (boundaryForwardProduct M s a K 1 0).coeff K = -(K : ℂ) * Complex.I ^ K ∧
    (boundaryForwardProduct M s a K 1 1).coeff K = Complex.I ^ K := by
  induction K with
  | zero => simp [boundaryForwardProduct]
  | succ K ih =>
    have hz (i j : Fin 2) : (boundaryForwardProduct M s a K i j).coeff (K + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt ((boundaryForwardProduct_degree M s a K i j).trans_lt (by omega))
    have ht (i j : Fin 2) := boundaryLinear_mul_top (a K)
      (boundaryForwardProduct M s a K i j) K (boundaryForwardProduct_degree ..)
    simp only [boundaryForwardProduct, Matrix.mul_apply, Fin.sum_univ_two,
      boundaryForwardStep, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      sub_mul, neg_mul, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, hz, mul_zero,
      add_zero, sub_zero, ht, ih.1, ih.2.1, ih.2.2.1, ih.2.2.2]
    push_cast
    simp only [pow_succ]
    constructor
    · ring
    constructor
    · trivial
    constructor <;> ring

theorem boundaryForwardStep_eval (M : ℝ) (s a : ℂ) (v : ℝ) (i j : Fin 2) :
    (boundaryForwardStep M s a i j).eval (v : ℂ) =
      forwardMatrix (M : ℂ) s (a + Complex.I * v) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [boundaryForwardStep, boundaryLinear, forwardMatrix]

/-- Evaluation of the symbolic boundary product gives the actual forward
matching matrix on a vertical spectral line. -/
theorem boundaryForwardProduct_eval (M : ℝ) (s q : ℂ) (v : ℝ) (K : ℕ)
    (i j : Fin 2) :
    (boundaryForwardProduct M s (fun n => q + n) K i j).eval (v : ℂ) =
      forwardProduct (M : ℂ) s (q + Complex.I * v) K i j := by
  induction K generalizing i j with
  | zero => fin_cases i <;> fin_cases j <;> simp [boundaryForwardProduct, forwardProduct]
  | succ K ih =>
    simp only [boundaryForwardProduct, forwardProduct, Matrix.mul_apply,
      Fin.sum_univ_two, eval_add, eval_mul, boundaryForwardStep_eval, ih]
    have h : q + (K : ℂ) + Complex.I * (v : ℂ) = q + Complex.I * v + K := by ring
    rw [h]

end DefocusingNLS

end OAI
