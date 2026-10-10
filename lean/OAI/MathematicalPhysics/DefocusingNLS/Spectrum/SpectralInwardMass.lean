import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOscillatoryEnergy

namespace OAI

/-! An inward complex slope gives scalar mass decay even at zeros. -/

namespace DefocusingNLS

theorem spectralComplex_inward_mass (z dz alpha : ℂ) (mu delta : ℝ)
    (hmu : 0 < mu) (_hdelta : 0 ≤ delta) (halpha : alpha.re ≤ -mu)
    (herr : ‖dz-alpha*z‖ ≤ delta) :
    2*(star z*dz).re ≤ -mu*Complex.normSq z+delta^2/mu := by
  have heq : (star z*dz).re = alpha.re*Complex.normSq z+(star z*(dz-alpha*z)).re := by
    simp only [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
      Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
    ring
  have hre := Complex.re_le_norm (star z*(dz-alpha*z))
  rw [norm_mul,norm_star] at hre
  have herr' : (star z*(dz-alpha*z)).re ≤ ‖z‖*delta :=
    hre.trans (mul_le_mul_of_nonneg_left herr (norm_nonneg _))
  have hyoung : 2*‖z‖*delta ≤ mu*Complex.normSq z+delta^2/mu := by
    rw [← Complex.sq_norm]
    apply (mul_le_mul_iff_right₀ hmu).mp
    have hsq := sq_nonneg (mu*‖z‖-delta)
    have hd : delta^2/mu*mu = delta^2 := div_mul_cancel₀ _ hmu.ne'
    nlinarith only [hsq,hd]
  have ha := mul_le_mul_of_nonneg_right halpha (Complex.normSq_nonneg z)
  rw [heq]
  linarith

end DefocusingNLS

end OAI
