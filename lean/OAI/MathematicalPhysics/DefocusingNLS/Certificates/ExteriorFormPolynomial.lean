import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorPolynomial
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryFormEvaluation

namespace OAI

/-! The certified K=5 polynomials are the actual transported exterior form. -/

open Polynomial Matrix
namespace DefocusingNLS.ExteriorCertificate
open GaussianEnclosure
open BoundaryCertificate (EnclosurePolynomial EnclosesState stateMatrix constant_sound)

attribute [local irreducible] state polynomialState

noncomputable def formPolynomial (z₀ : ℤ) (b : ℝ) (i j : Fin 2) : Polynomial ℂ :=
  let T := stateMatrix (polynomialState z₀ b 5)
  C (500000000 : ℂ)*conjugatePolynomial (T 0 i)*T 0 j+
    inputS z₀*(conjugatePolynomial (T 0 i)*T 1 j-conjugatePolynomial (T 1 i)*T 0 j)

private theorem hermitian_sound (z₀ : ℤ)
    {x y z w : EnclosurePolynomial} {p q r t : Polynomial ℂ}
    (hx : EnclosesPolynomial x p) (hy : EnclosesPolynomial y q)
    (hz : EnclosesPolynomial z r) (hw : EnclosesPolynomial w t) :
    EnclosesPolynomial (hermitian z₀ x y z w)
      (C (500000000 : ℂ)*conjugatePolynomial p*r+
        inputS z₀*(conjugatePolynomial p*t-conjugatePolynomial q*r)) := by
  exact addPolynomial_sound
    (mulPolynomial_sound (mulPolynomial_sound (constant_sound 500000000)
      (conjPolynomial_sound hx)) hz)
    (mulPolynomial_sound (inputS_sound z₀)
      (subPolynomial_sound (mulPolynomial_sound (conjPolynomial_sound hx) hw)
        (mulPolynomial_sound (conjPolynomial_sound hy) hz)))

theorem diagonal_sound (z₀ : ℤ) (b : ℝ) (hb : |100000000*b-33477607| ≤ 2) :
    EnclosesPolynomial (diagonal z₀) (formPolynomial z₀ b 1 1) := by
  obtain ⟨_,hx,_,hy⟩ := state_sound z₀ b hb 5
  exact hermitian_sound z₀ hx hy hx hy

theorem lowerOffDiagonal_sound (z₀ : ℤ) (b : ℝ) (hb : |100000000*b-33477607| ≤ 2) :
    EnclosesPolynomial (lowerOffDiagonal z₀) (formPolynomial z₀ b 1 0) := by
  obtain ⟨hx₀,hx₁,hy₀,hy₁⟩ := state_sound z₀ b hb 5
  exact hermitian_sound z₀ hx₁ hy₁ hx₀ hy₀

private theorem forwardFormEntry_real_scaling (h a M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    forwardFormEntry (h*M) ((h : ℂ)*s) ((a : ℂ) • T) i j =
      ((h*a^2 : ℝ) : ℂ)*forwardFormEntry M s T i j := by
  simp only [forwardFormEntry, Matrix.smul_apply, smul_eq_mul, star_mul,
    Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

/-- The degree-truncated checks must be applied to this same coherent form. -/
theorem formPolynomial_eval (z₀ : ℤ) (b v : ℝ) (i j : Fin 2) :
    (formPolynomial z₀ b i j).eval (v : ℂ) =
      (100000000 : ℂ)^11*
        forwardFormEntry 5 (Complex.I*(((z₀ : ℝ)/100000000+v : ℝ) : ℂ))
          (forwardProduct 5 (Complex.I*(((z₀ : ℝ)/100000000+v : ℝ) : ℂ))
            (-Complex.I*(b : ℂ)) 5) i j := by
  let T := forwardProduct 5 (Complex.I*(((z₀ : ℝ)/100000000+v : ℝ) : ℂ))
    (-Complex.I*(b : ℂ)) 5
  have he : (fun i j => (stateMatrix (polynomialState z₀ b 5) i j).eval (v : ℂ)) =
      (100000000 : ℂ)^5 • T := by
    ext i j
    exact polynomialState_eval_scaled z₀ b v 5 i j
  unfold formPolynomial
  simp only [eval_add,eval_mul,eval_sub,eval_C,conjugatePolynomial_eval_real]
  rw [inputS_eval_scaled]
  change forwardFormEntry 500000000
    ((100000000 : ℂ)*(Complex.I*(((z₀ : ℝ)/100000000+v : ℝ) : ℂ)))
    (fun i j => (stateMatrix (polynomialState z₀ b 5) i j).eval (v : ℂ)) i j = _
  rw [show (500000000 : ℝ) = 100000000*5 by norm_num, he]
  have hscale := forwardFormEntry_real_scaling (100000000 : ℝ)
    ((100000000 : ℝ)^5) 5 (Complex.I*(((z₀ : ℝ)/100000000+v : ℝ) : ℂ)) T i j
  push_cast at hscale ⊢
  rw [hscale]
  dsimp only [T]
  push_cast
  congr 1
  ring

end DefocusingNLS.ExteriorCertificate

end OAI
