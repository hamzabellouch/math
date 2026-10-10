import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorCertificateRecipe
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryEnclosureStateLink

namespace OAI

/-! The coherent spatial polynomial enclosed by the K=5 exterior computation. -/

open Polynomial Matrix
namespace DefocusingNLS.ExteriorCertificate
open GaussianEnclosure
open BoundaryCertificate (PolynomialState EnclosesState polynomialStep stateMatrix
  polynomialStep_matrix constant_sound)

noncomputable def inputS (z₀ : ℤ) : Polynomial ℂ :=
  C (Complex.I*(z₀ : ℂ))+X*C (Complex.I*(100000000 : ℂ))

noncomputable def inputT (n : ℕ) (b : ℝ) : Polynomial ℂ :=
  C (((100000000*(n : ℤ) : ℤ) : ℂ)-Complex.I*((100000000 : ℝ)*b : ℝ))

noncomputable def polynomialState (z₀ : ℤ) (b : ℝ) : ℕ → PolynomialState
  | 0 => ((1,0),(0,1))
  | n+1 => polynomialStep (C (500000000 : ℂ)) (inputS z₀) (inputT n b)
      (polynomialState z₀ b n)

theorem inputS_sound (z₀ : ℤ) :
    EnclosesPolynomial [BoundaryCertificate.coefficient 0 z₀ 0,
      BoundaryCertificate.coefficient 0 100000000 0] (inputS z₀) := by
  refine ⟨Complex.I*(z₀ : ℂ), C (Complex.I*(100000000 : ℂ)), ?_, ?_, rfl⟩
  · simp [Encloses, BoundaryCertificate.coefficient, GaussianInt.toComplex_def', mul_comm]
  · refine ⟨Complex.I*(100000000 : ℂ),0,?_,rfl,by simp⟩
    norm_num [Encloses, BoundaryCertificate.coefficient, GaussianInt.toComplex_def', mul_comm]

theorem inputT_sound (n : ℕ) (b : ℝ) (hb : |100000000*b-33477607| ≤ 2) :
    EnclosesPolynomial [BoundaryCertificate.coefficient (100000000*(n : ℤ)) (-33477607) 2]
      (inputT n b) := by
  refine ⟨(((100000000*(n : ℤ) : ℤ) : ℂ)-Complex.I*(100000000*b : ℝ)),
    0,?_,rfl,by simp only [inputT,mul_zero,add_zero]⟩
  change ‖(((100000000*(n : ℤ) : ℤ) : ℂ)-Complex.I*(100000000*b : ℝ))-
    ((⟨100000000*(n : ℤ),-33477607⟩ : GaussianInt) : ℂ)‖ ≤ 2
  have he : (((100000000*(n : ℤ) : ℤ) : ℂ)-Complex.I*(100000000*b : ℝ))-
      ((⟨100000000*(n : ℤ),-33477607⟩ : GaussianInt) : ℂ) =
        ((100000000*b-33477607 : ℝ) : ℂ)*(-Complex.I) := by
    rw [GaussianInt.toComplex_def']
    push_cast
    ring
  rw [he, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact hb

theorem step_sound (z₀ : ℤ) (n : ℕ) (b : ℝ)
    (hb : |100000000*b-33477607| ≤ 2)
    {xy : BoundaryCertificate.State} {pq : PolynomialState} (h : EnclosesState xy pq) :
    EnclosesState (step z₀ n xy)
      (polynomialStep (C (500000000 : ℂ)) (inputS z₀) (inputT n b) pq) := by
  obtain ⟨hx₀,hx₁,hy₀,hy₁⟩ := h
  have ht := inputT_sound n b hb
  have hs := inputS_sound z₀
  have hM := constant_sound 500000000
  have hd := subPolynomial_sound ht hM
  have hx₀' := addPolynomial_sound (mulPolynomial_sound ht hx₀) (mulPolynomial_sound hs hy₀)
  have hx₁' := addPolynomial_sound (mulPolynomial_sound ht hx₁) (mulPolynomial_sound hs hy₁)
  exact ⟨hx₀',hx₁',subPolynomial_sound (mulPolynomial_sound hd hy₀) hx₀',
    subPolynomial_sound (mulPolynomial_sound hd hy₁) hx₁'⟩

theorem state_sound (z₀ : ℤ) (b : ℝ) (hb : |100000000*b-33477607| ≤ 2) (n : ℕ) :
    EnclosesState (state z₀ n) (polynomialState z₀ b n) := by
  induction n with
  | zero =>
    exact ⟨by simpa [state,polynomialState] using constant_sound 1,
      by simpa [state,polynomialState] using constant_sound 0,
      by simpa [state,polynomialState] using constant_sound 0,
      by simpa [state,polynomialState] using constant_sound 1⟩
  | succ n ih => exact step_sound z₀ n b hb ih

theorem inputT_eval_scaled (n : ℕ) (b v : ℝ) :
    (inputT n b).eval (v : ℂ) =
      (100000000 : ℂ)*(-Complex.I*(b : ℂ)+(n : ℂ)) := by
  simp only [inputT, eval_C]
  push_cast
  ring

theorem inputS_eval_scaled (z₀ : ℤ) (v : ℝ) :
    (inputS z₀).eval (v : ℂ) =
      (100000000 : ℂ)*(Complex.I*(((z₀ : ℝ)/100000000+v : ℝ) : ℂ)) := by
  simp only [inputS, eval_add, eval_mul, eval_C, eval_X]
  push_cast
  ring

attribute [local irreducible] polynomialState

/-- Evaluation gives the actual forward matrix, with its exact integer scale. -/
theorem polynomialState_eval_scaled (z₀ : ℤ) (b v : ℝ) (N : ℕ) (i j : Fin 2) :
    (stateMatrix (polynomialState z₀ b N) i j).eval (v : ℂ) =
      (100000000 : ℂ)^N*
        forwardProduct 5 (Complex.I*(((z₀ : ℝ)/100000000+v : ℝ) : ℂ))
          (-Complex.I*(b : ℂ)) N i j := by
  induction N generalizing i j with
  | zero => fin_cases i <;> fin_cases j <;> simp [polynomialState,stateMatrix,forwardProduct]
  | succ N ih =>
    rw [polynomialState, polynomialStep_matrix]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, eval_add, eval_mul, ih]
    have ht := inputT_eval_scaled N b v
    have hs := inputS_eval_scaled z₀ v
    fin_cases i <;> fin_cases j <;>
      simp [forwardProduct, forwardMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        eval_sub, eval_neg, eval_C, ht, hs, pow_succ] <;> ring

end DefocusingNLS.ExteriorCertificate

end OAI
