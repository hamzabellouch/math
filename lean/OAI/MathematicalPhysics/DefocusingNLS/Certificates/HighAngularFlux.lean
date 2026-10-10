import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularSquare

namespace OAI

/-! Algebraic flux identities underlying the high-angular exclusion. -/

namespace DefocusingNLS

/-- The real flux derivative before completing the kinetic square. -/
theorem highAngular_raw_flux (A A' C V E U U' U'' : ℂ)
    (hODE : -A*U''-(A'-C*A)*U'+V*U=E*U) :
    (A'*star U*U'+A*star U'*U'+A*star U*U'').re =
      A.re*Complex.normSq U'+(C*A*star U*U').re+
        (V.re-E.re)*Complex.normSq U := by
  have h := congrArg (fun z : ℂ => (star U*z).re) hODE
  simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.neg_re,Complex.neg_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,Complex.normSq_apply] at h ⊢
  linear_combination -h

/-- Adding the correction to the boundary flux produces exactly the bulk
potential from the manuscript. -/
theorem highAngular_corrected_flux (L N α αL' θ' N' h : ℝ)
    (A' V E U U' U'' : ℂ) (hh : h=1 ∨ h= -1)
    (hODE : -((L : ℂ)+Complex.I*(h*N : ℝ))*U''-
      (A'-Complex.I*(h*θ' : ℝ)*((L : ℂ)+Complex.I*(h*N : ℝ)))*U'+V*U=E*U) :
    (A'*star U*U'+((L : ℂ)+Complex.I*(h*N : ℝ))*star U'*U'+
      ((L : ℂ)+Complex.I*(h*N : ℝ))*star U*U'').re+
      (αL'+θ'*N'/2)*Complex.normSq U+
      (α*L+θ'*N/2)*(2*(star U*U').re) =
    L*Complex.normSq (U'+((α : ℂ)-Complex.I*(h*θ'/2 : ℝ))*U)+
      (V.re-E.re+αL'+θ'*N'/2-L*(α^2+θ'^2/4))*Complex.normSq U := by
  rw [highAngular_raw_flux _ _ _ _ _ _ _ _ hODE]
  have hA : ((L : ℂ)+Complex.I*(h*N : ℝ)).re = L := by simp
  rw [hA,highAngular_completed_square L N α θ' h U U' hh]
  ring

end DefocusingNLS

end OAI
