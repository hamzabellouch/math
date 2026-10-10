import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorHermitianDisk

namespace OAI

/-! Determinant of the transported two-dimensional Hermitian form. -/

namespace DefocusingNLS

private theorem forwardFormEntry_determinant_complex (M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) ℂ) :
    forwardFormEntry M s T 0 0*forwardFormEntry M s T 1 1-
      forwardFormEntry M s T 0 1*forwardFormEntry M s T 1 0 =
      s^2*T.det*star T.det := by
  simp only [forwardFormEntry,Matrix.det_fin_two,star_sub,star_mul]
  ring

theorem forwardFormEntry_determinant (M Z : ℝ) (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (forwardFormEntry M (Complex.I*(Z : ℂ)) T 0 0).re*
      (forwardFormEntry M (Complex.I*(Z : ℂ)) T 1 1).re-
      Complex.normSq (forwardFormEntry M (Complex.I*(Z : ℂ)) T 0 1) =
      -Z^2*Complex.normSq T.det := by
  have hs : (Complex.I*(Z : ℂ)).re = 0 := by simp
  have h := forwardFormEntry_determinant_complex M (Complex.I*(Z : ℂ)) T
  rw [forwardFormEntry_diagonal M _ T hs 0,
    forwardFormEntry_diagonal M _ T hs 1,
    ← forwardFormEntry_hermitian M _ T hs 1 0] at h
  have hr := congrArg Complex.re h
  simp only [Complex.sub_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
    Complex.I_re,Complex.I_im,pow_two,Complex.normSq_apply] at hr ⊢
  nlinarith [hr]

end DefocusingNLS

end OAI
