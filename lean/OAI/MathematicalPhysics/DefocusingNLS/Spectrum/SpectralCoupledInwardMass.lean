import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralInwardMass

namespace OAI

/-! Absorb the self-coupling part of a small local Robin error. -/

namespace DefocusingNLS

theorem spectralComplex_coupled_inward_mass (z dz w alpha : ℂ) (mu eps : ℝ)
    (hmu : 0 < mu) (heps : 0 ≤ eps) (hsmall : eps ≤ 1/2)
    (halpha : alpha.re ≤ -mu)
    (herr : ‖dz-alpha*z‖ ≤ eps*mu*(‖z‖+‖w‖)) :
    2*(star z*dz).re ≤ -(mu/2)*Complex.normSq z+2*eps^2*mu*Complex.normSq w := by
  have hm := spectralComplex_inward_mass z dz alpha mu (eps*mu*(‖z‖+‖w‖)) hmu
    (by positivity) halpha herr
  have hs : (‖z‖+‖w‖)^2 ≤ 2*(‖z‖^2+‖w‖^2) := by nlinarith [sq_nonneg (‖z‖-‖w‖)]
  have hbound : (eps*mu*(‖z‖+‖w‖))^2/mu ≤ 2*eps^2*mu*(‖z‖^2+‖w‖^2) := by
    apply (div_le_iff₀ hmu).mpr
    have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ eps^2*mu^2)
    nlinarith only [hh]
  have hes : 2*eps^2 ≤ 1/2 := by nlinarith
  have habs := mul_le_mul_of_nonneg_right hes (mul_nonneg hmu.le (sq_nonneg ‖z‖))
  simp only [← Complex.sq_norm] at hm ⊢
  nlinarith only [hm,hbound,habs]

end DefocusingNLS

end OAI
