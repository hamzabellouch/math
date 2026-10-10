import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarFlux
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellNorm

namespace OAI

/-! Quantitative stability of the complex flux in the shell norm, used to
retain a nonzero outgoing flux under the WKB and Airy limits. -/

namespace DefocusingNLS

theorem spectralScalarFlux_continuous : Continuous spectralScalarFlux := by
  exact Complex.continuous_im.comp (continuous_fst.star.mul continuous_snd)

theorem spectralScalarFlux_sub_bound (k : ℝ) (hk : 0 < k) (u v : ℂ × ℂ) :
    |spectralScalarFlux u - spectralScalarFlux v| ≤
      spectralShellNorm k (u-v) * (spectralShellNorm k u + spectralShellNorm k v) := by
  have he : star u.1*u.2 - star v.1*v.2 =
      star (u.1-v.1)*u.2 + star v.1*(u.2-v.2) := by
    rw [star_sub]
    ring
  have hi : |spectralScalarFlux u - spectralScalarFlux v| ≤
      ‖u.1-v.1‖*‖u.2‖ + ‖v.1‖*‖u.2-v.2‖ := by
    calc
      _ = |(star u.1*u.2 - star v.1*v.2).im| := by
        simp only [spectralScalarFlux,Complex.sub_im]
      _ ≤ ‖star u.1*u.2 - star v.1*v.2‖ := Complex.abs_im_le_norm _
      _ = ‖star (u.1-v.1)*u.2 + star v.1*(u.2-v.2)‖ := by rw [he]
      _ ≤ ‖star (u.1-v.1)*u.2‖ + ‖star v.1*(u.2-v.2)‖ := norm_add_le _ _
      _ = _ := by simp only [norm_mul,norm_star]
  have h₁ := mul_le_mul (spectralShellNorm_value k hk (u-v))
    (spectralShellNorm_slope k hk u) (norm_nonneg u.2)
    (div_nonneg (spectralShellNorm_nonneg k hk.le (u-v)) hk.le)
  have h₂ := mul_le_mul (spectralShellNorm_value k hk v)
    (spectralShellNorm_slope k hk (u-v)) (norm_nonneg (u.2-v.2))
    (div_nonneg (spectralShellNorm_nonneg k hk.le v) hk.le)
  change ‖u.1-v.1‖*‖u.2‖ ≤ (spectralShellNorm k (u-v)/k)*(k*spectralShellNorm k u) at h₁
  change ‖v.1‖*‖u.2-v.2‖ ≤ (spectralShellNorm k v/k)*(k*spectralShellNorm k (u-v)) at h₂
  have he₁ : (spectralShellNorm k (u-v)/k)*(k*spectralShellNorm k u) =
      spectralShellNorm k (u-v)*spectralShellNorm k u := by field_simp
  have he₂ : (spectralShellNorm k v/k)*(k*spectralShellNorm k (u-v)) =
      spectralShellNorm k v*spectralShellNorm k (u-v) := by field_simp
  rw [he₁] at h₁
  rw [he₂] at h₂
  nlinarith

end DefocusingNLS

end OAI
