import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralComplexSqrtScale
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningScaledNorm

namespace OAI

/-! Exact identification of the rescaled growing projection with the
physical WKB coefficient at the forbidden endpoint. -/

namespace DefocusingNLS

theorem spectralTurning_sqrt_momentum_scale (d : ℝ) (p : ℂ)
    (hd : 0 < d) (hp : 0 < p.re) :
    Complex.sqrt ((d : ℂ)*p) = (Real.sqrt d : ℂ)*Complex.sqrt p := by
  have hs : (Real.sqrt d : ℂ)^2 = (d : ℂ) := by exact_mod_cast Real.sq_sqrt hd.le
  simpa only [hs] using spectralComplexSqrt_scale (Real.sqrt d) (Real.sqrt_pos.mpr hd) p hp

theorem spectralTurning_projection_identity (d g : ℝ) (p : ℂ) (u : ℂ × ℂ)
    (hd : 0 < d) (hp : 0 < p.re) :
    let v := (u.1/(Real.sqrt d : ℂ),-(Real.sqrt d : ℂ)*u.2)
    (v.2+((d : ℂ)*p+((d^3*g : ℝ) : ℂ)/(4*((d : ℂ)*p)^2))*v.1)/
      (2*Complex.sqrt ((d : ℂ)*p)) =
      spectralScalarWronskian ((Complex.sqrt p)⁻¹,
        (p+(g : ℂ)/(4*p^2))*(Complex.sqrt p)⁻¹) u/(-2) := by
  dsimp only
  have hpn : p ≠ 0 := by intro he; simp only [he,Complex.zero_re] at hp; linarith
  have hs : (Real.sqrt d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hd).ne'
  have hdn : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hps := spectralComplexSqrt_ne_zero p hpn
  have hsq : (Real.sqrt d : ℂ)^2 = (d : ℂ) := by exact_mod_cast Real.sq_sqrt hd.le
  rw [spectralTurning_sqrt_momentum_scale d p hd hp]
  dsimp only [spectralScalarWronskian]
  push_cast
  rw [← hsq]
  field_simp [hs,hpn,hps]; ring

theorem spectralTurning_projection_norm_scale (d : ℝ) (p : ℂ) (u : ℂ × ℂ)
    (hd : 0 < d) (hp : p ≠ 0) :
    spectralShellNorm (Real.sqrt ‖(d : ℂ)*p‖)
      (u.1/(Real.sqrt d : ℂ),-(Real.sqrt d : ℂ)*u.2) =
      spectralShellNorm (Real.sqrt ‖p‖) u := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd,Real.sqrt_mul hd.le]
  exact spectralShellNorm_scale (Real.sqrt d) (Real.sqrt ‖p‖)
    (Real.sqrt_pos.mpr hd) (Real.sqrt_pos.mpr (norm_pos_iff.mpr hp)) u

end DefocusingNLS

end OAI
