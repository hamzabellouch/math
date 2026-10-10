import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousInvariantSemigroup
import Mathlib.Analysis.Complex.Trigonometric

namespace OAI

/-! # Generator eigenvectors and the contour radius

The exponential representation identifies generator eigenvectors with step
multipliers and converts their modulus into a real-part estimate.
-/

namespace DefocusingNLS

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem operator_exp_apply_of_eigenvector (G : E →L[ℂ] E) (lam : ℂ) (u : E)
    (hu : G u = lam • u) : NormedSpace.exp G u = Complex.exp lam • u := by
  have hp (n : ℕ) : (G ^ n) u = lam ^ n • u := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hu]
        simp only [smul_smul, pow_succ, mul_comm]
  have hs := (ContinuousLinearMap.apply ℂ E u).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) G)
  have ht := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) lam).smul_const u
  have he : NormedSpace.exp G u = NormedSpace.exp lam • u := by
    apply HasSum.unique hs
    convert ht using 1
    ext n
    simp only [ContinuousLinearMap.apply_apply, smul_apply,
      hp, smul_smul, smul_eq_mul]
  simpa only [← Complex.exp_eq_exp_ℂ] using he

theorem real_smul_operator_exp_apply_of_eigenvector (G : E →L[ℂ] E)
    (lam : ℂ) (u : E) (hu : G u = lam • u) (t : ℝ) :
    NormedSpace.exp (t • G) u = Complex.exp ((t : ℂ) * lam) • u := by
  apply operator_exp_apply_of_eigenvector
  rw [smul_apply, hu, ← smul_assoc, Complex.real_smul]

theorem generator_realPart_gt_of_step_modulus (lam : ℂ) (t γ : ℝ)
    (ht : 0 < t) (hmod : Real.exp (-γ * t) < ‖Complex.exp ((t : ℂ) * lam)‖) :
    -γ < lam.re := by
  rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hmod
  have h := Real.exp_lt_exp.mp hmod
  nlinarith

end

end DefocusingNLS

end OAI
