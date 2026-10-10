import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicEigenmode

namespace OAI

/-! For real spectral and angular parameters, conjugating the first circular
equation gives the second one for a real symmetry generator. -/

namespace DefocusingNLS

theorem harmonicRadialEigenpair_of_real_first (a b : ℝ) (m : ℕ) (Q f : ℝ → ℂ)
    (eta lam : ℝ)
    (hf : ∀ r : ℝ, 0<r → (lam : ℂ)*f r =
      Complex.I*(deriv (deriv f) r+(11/r : ℝ)*deriv f r-(eta : ℂ)/(r^2 : ℝ)*f r)-
      (r/2 : ℝ)*deriv f r+(-(a : ℂ)+Complex.I*(b : ℂ))*f r-Complex.I*
      ((((m+1 : ℕ) : ℂ)*Q r^m*star (Q r)^m)*f r+
        ((m : ℂ)*Q r^(m+1)*star (Q r)^(m-1))*star (f r))) :
    IsHarmonicRadialEigenpair a b m Q (eta : ℂ) (lam : ℂ) f (fun r => star (f r)) := by
  intro r hr
  refine ⟨hf r hr,?_⟩
  have hc := congrArg star (hf r hr)
  simp only [star_sub,star_add,star_mul,star_div₀,star_neg,Complex.star_def,
    Complex.conj_I,Complex.conj_ofReal] at hc
  simp only [starRingEnd_apply] at hc
  simp only [deriv.star']
  simp only [star_mul,star_star] at hc ⊢
  linear_combination hc

end DefocusingNLS

end OAI
