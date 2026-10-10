import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarFlux

namespace OAI

/-! An outgoing scalar slope controls the remaining boundary value by
the total flux and the already vanishing positive channel. -/

namespace DefocusingNLS

theorem spectralOutgoing_flux_coercivity (z w dz dw alpha : ℂ) (nu eps : ℝ)
    (hnu : 0 ≤ nu) (heps : 0 ≤ eps) (hsmall : eps ≤ 1/16)
    (ha : alpha.im ≤ -nu/4)
    (herr : ‖dw-alpha*w‖ ≤ eps*nu*(‖z‖+‖w‖)) :
    (nu*‖w‖)^2 ≤ 8*(nu*|spectralScalarFlux (z,dz)+spectralScalarFlux (w,dw)|+
      (nu*‖z‖)*‖dz‖)+(nu*‖z‖)^2 := by
  have hidentity : spectralScalarFlux (w,dw) = alpha.im*‖w‖^2+(star w*(dw-alpha*w)).im := by
    rw [Complex.sq_norm]
    simp only [spectralScalarFlux,Complex.star_def,Complex.mul_re,Complex.mul_im,
      Complex.sub_re,Complex.sub_im,Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
    ring
  have he : |(star w*(dw-alpha*w)).im| ≤ ‖w‖*(eps*nu*(‖z‖+‖w‖)) := by
    calc
      _ ≤ ‖star w*(dw-alpha*w)‖ := Complex.abs_im_le_norm _
      _ = ‖w‖*‖dw-alpha*w‖ := by rw [norm_mul,norm_star]
      _ ≤ _ := mul_le_mul_of_nonneg_left herr (norm_nonneg _)
  have hp : |spectralScalarFlux (z,dz)| ≤ ‖z‖*‖dz‖ := by
    exact (Complex.abs_im_le_norm _).trans_eq (by rw [norm_mul,norm_star])
  have ht : -spectralScalarFlux (w,dw) ≤
      |spectralScalarFlux (z,dz)+spectralScalarFlux (w,dw)|+‖z‖*‖dz‖ := by
    have h := neg_le_abs (spectralScalarFlux (z,dz)+spectralScalarFlux (w,dw))
    linarith [(le_abs_self (spectralScalarFlux (z,dz))).trans hp]
  have hs : -spectralScalarFlux (w,dw) ≥ nu/4*‖w‖^2-‖w‖*(eps*nu*(‖z‖+‖w‖)) := by
    have ham := mul_le_mul_of_nonneg_right ha (sq_nonneg ‖w‖)
    linarith [(le_abs_self _).trans he]
  have hscaled := mul_le_mul_of_nonneg_left (hs.trans ht) hnu
  have hprod : (nu*‖w‖)*(nu*‖z‖) ≤ (nu*‖z‖)^2+(nu*‖w‖)^2 := by
    nlinarith [sq_nonneg (nu*‖z‖-nu*‖w‖),sq_nonneg (nu*‖z‖),sq_nonneg (nu*‖w‖)]
  have herr2 : eps*((nu*‖w‖)*(nu*‖z‖)+(nu*‖w‖)^2) ≤
      (1/16)*((nu*‖z‖)^2+2*(nu*‖w‖)^2) := by
    calc
      _ ≤ eps*((nu*‖z‖)^2+2*(nu*‖w‖)^2) := by nlinarith [mul_le_mul_of_nonneg_left hprod heps]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (by positivity)
  nlinarith only [hscaled,herr2,sq_nonneg (nu*‖z‖)]

end DefocusingNLS

end OAI
