import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarFluxStability

namespace OAI

/-! An explicit flux lower bound survives a small error in the weighted
Cauchy data, with constants suitable for the outgoing WKB comparison. -/

namespace DefocusingNLS

theorem spectralScalarFlux_lower_of_close (h k c A B delta : ℝ) (u v : ℂ × ℂ)
    (hh : h^2 = 1) (hk : 0 < k)
    (hflux : c ≤ h*spectralScalarFlux v)
    (hu : spectralShellNorm k u ≤ A) (hv : spectralShellNorm k v ≤ B)
    (hclose : spectralShellNorm k (u-v) ≤ delta) :
    c-delta*(A+B) ≤ h*spectralScalarFlux u := by
  have hhabs : |h| = 1 := by nlinarith [sq_abs h,abs_nonneg h]
  have hd0 : 0 ≤ delta := (spectralShellNorm_nonneg k hk.le _).trans hclose
  have hdiff : |h*(spectralScalarFlux u-spectralScalarFlux v)| ≤ delta*(A+B) := by
    rw [abs_mul,hhabs,one_mul]
    apply (spectralScalarFlux_sub_bound k hk u v).trans
    exact mul_le_mul hclose (add_le_add hu hv)
      (add_nonneg (spectralShellNorm_nonneg k hk.le _) (spectralShellNorm_nonneg k hk.le _)) hd0
  have hl := (abs_le.mp hdiff).1
  nlinarith

end DefocusingNLS

end OAI
