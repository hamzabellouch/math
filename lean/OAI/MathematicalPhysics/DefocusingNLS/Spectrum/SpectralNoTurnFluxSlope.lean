import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnComparison

namespace OAI

/-! The normalized outgoing slope has a strictly negative imaginary part. -/

namespace DefocusingNLS

theorem spectralNoTurn_slope_im (alpha : ℂ) (k nu : ℝ)
    (hk : 0 < k) (hknu : nu/2 ≤ k)
    (hclose : ‖alpha/(k : ℂ)+Complex.I‖ ≤ 1/2) : alpha.im ≤ -nu/4 := by
  have hi := (le_abs_self (alpha/(k : ℂ)+Complex.I).im).trans
    ((Complex.abs_im_le_norm _).trans hclose)
  have heq : (alpha/(k : ℂ)+Complex.I).im = alpha.im/k+1 := by
    simp only [Complex.add_im,Complex.I_im,Complex.div_ofReal_im]
  rw [heq] at hi
  have hb : alpha.im/k ≤ -(1/2 : ℝ) := by linarith
  have hm := (div_le_iff₀ hk).mp hb
  linarith

end DefocusingNLS

end OAI
