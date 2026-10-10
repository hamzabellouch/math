import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ForwardHermitianForm

namespace OAI

/-! The square completion in the high-angular multiplier identity. -/

namespace DefocusingNLS

theorem highAngular_completed_square (L N α θ' h : ℝ) (U V : ℂ)
    (hh : h=1 ∨ h= -1) :
    L*Complex.normSq V+
      ((Complex.I*(h*θ' : ℝ))*((L : ℂ)+Complex.I*(h*N : ℝ))*star U*V).re =
      L*Complex.normSq (V+((α : ℂ)-Complex.I*(h*θ'/2 : ℝ))*U)-
        (α*L+θ'*N/2)*(2*(star U*V).re)-
        L*(α^2+θ'^2/4)*Complex.normSq U := by
  rcases hh with rfl | rfl <;>
    simp only [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.add_re,
      Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.star_def,Complex.conj_re,
      Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im] <;>
    ring

end DefocusingNLS

end OAI
