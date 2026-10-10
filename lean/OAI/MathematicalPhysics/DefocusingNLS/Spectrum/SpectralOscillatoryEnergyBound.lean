import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOscillatoryEnergy

namespace OAI

/-! A uniform differential energy bound on the oscillatory exterior shell. -/

namespace DefocusingNLS

theorem spectralScalarFlux_energy_bound (q : ℂ × ℂ) :
    2*|spectralScalarFlux q| ≤ Complex.normSq q.1+Complex.normSq q.2 := by
  have hh := Complex.abs_im_le_norm (star q.1*q.2)
  rw [norm_mul,norm_star] at hh
  rw [← Complex.sq_norm,← Complex.sq_norm]
  dsimp only [spectralScalarFlux]
  nlinarith [sq_nonneg (‖q.1‖-‖q.2‖)]

theorem spectralOscillatoryEnergy_deriv_bound (F Fp gamma K G : ℝ)
    (q : ℂ × ℂ) (forcing : ℂ) (hF : 1 ≤ F) (hK : 0 ≤ K)
    (hFp : Fp ≤ K*F) (hG : |gamma| ≤ G) :
    Fp*Complex.normSq q.1-2*gamma*spectralScalarFlux q+2*(star q.2*forcing).re ≤
      (K+2*G+1)*spectralOscillatoryEnergy F q+‖forcing‖^2 := by
  have hG0 : 0 ≤ G := (abs_nonneg gamma).trans hG
  have hq1 := Complex.normSq_nonneg q.1
  have hq2 := Complex.normSq_nonneg q.2
  have hmass : Complex.normSq q.1 ≤ spectralOscillatoryEnergy F q := by
    dsimp only [spectralOscillatoryEnergy]
    nlinarith
  have hvel : Complex.normSq q.2 ≤ spectralOscillatoryEnergy F q := by
    dsimp only [spectralOscillatoryEnergy]
    nlinarith
  have hlead : Fp*Complex.normSq q.1 ≤ K*spectralOscillatoryEnergy F q := by
    have hh := mul_le_mul_of_nonneg_right hFp hq1
    dsimp only [spectralOscillatoryEnergy]
    nlinarith
  have hflux : -2*gamma*spectralScalarFlux q ≤ G*(Complex.normSq q.1+Complex.normSq q.2) := by
    calc
      _ ≤ |-2*gamma*spectralScalarFlux q| := le_abs_self _
      _ = |gamma| *(2*|spectralScalarFlux q|) := by rw [abs_mul,abs_mul]; norm_num; ring
      _ ≤ G*(Complex.normSq q.1+Complex.normSq q.2) :=
        mul_le_mul hG (spectralScalarFlux_energy_bound q) (by positivity) hG0
  have hflux' : -2*gamma*spectralScalarFlux q ≤ 2*G*spectralOscillatoryEnergy F q :=
    hflux.trans (by nlinarith [mul_le_mul_of_nonneg_left (add_le_add hmass hvel) hG0])
  have hforcing : 2*(star q.2*forcing).re ≤ Complex.normSq q.2+‖forcing‖^2 := by
    have hh := Complex.re_le_norm (star q.2*forcing)
    rw [norm_mul,norm_star] at hh
    rw [← Complex.sq_norm]
    nlinarith [sq_nonneg (‖q.2‖-‖forcing‖)]
  nlinarith

end DefocusingNLS

end OAI
