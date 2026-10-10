import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalLiouvillePair
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarModulus

namespace OAI

/-! The radial Liouville momentum has zero right limit at the regular
origin, despite the harmless value assigned to log at zero. -/

open Set Filter Topology
namespace DefocusingNLS

private theorem transformed_momentum (A S u v : ℂ) :
    (star (A*u)*(A*(v+S*u))).re =
      ‖A‖^2*((star u*v).re+S.re*‖u‖^2) := by
  rw [Complex.sq_norm,Complex.sq_norm]
  simp only [Complex.star_def,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
  ring

theorem spectralLiouville_momentum_formula (h r : ℝ) (hr : 0 < r) (u v : ℂ) :
    spectralScalarMomentum
      (homogeneousSpectralLocalizationFactor h r*u,
        homogeneousSpectralLocalizationFactor h r*(v+homogeneousSpectralLocalizationSlope h r*u)) =
      r^11*(star u*v).re+(11/2 : ℝ)*r^10*‖u‖^2 := by
  have hnorm : ‖homogeneousSpectralLocalizationFactor h r‖^2 = r^11 := by
    rw [homogeneousSpectralLocalizationFactor_norm h r hr,← Real.rpow_mul_natCast hr.le]
    norm_num
  have hS : (homogeneousSpectralLocalizationSlope h r).re = 11/(2*r) := by
    have hc : (11/(2*(r : ℂ)) : ℂ) = ((11/(2*r) : ℝ) : ℂ) := by push_cast; rfl
    rw [homogeneousSpectralLocalizationSlope,hc]
    norm_num [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.div_re]
    field_simp [hr.ne']
    norm_num
  rw [spectralScalarMomentum,transformed_momentum,hnorm,hS]
  field_simp [hr.ne']

theorem spectralLiouville_momentum_origin (h : ℝ) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    Tendsto (fun r => spectralScalarMomentum
      (homogeneousSpectralLocalizationState h (fun t => (f t,g t)) r))
      (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (fun r : ℝ => r^11*(star (f r)*g r).re+
      (11/2 : ℝ)*r^10*‖f r‖^2) := by fun_prop
  have ht : Tendsto (fun r : ℝ => r^11*(star (f r)*g r).re+
      (11/2 : ℝ)*r^10*‖f r‖^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (spectralLiouville_momentum_formula h r hr (f r) (g r)).symm

theorem spectralPhysicalLiouvillePair_momentum_origin (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    Tendsto (fun r => spectralScalarMomentum (spectralPhysicalLiouvillePair f g r).1+
      spectralScalarMomentum (spectralPhysicalLiouvillePair f g r).2) (𝓝[>] 0) (𝓝 0) := by
  simpa only [spectralPhysicalLiouvillePair,add_zero] using
    (spectralLiouville_momentum_origin 1 f (deriv f) hf.continuous
      (hf.continuous_deriv (by norm_num))).add
    (spectralLiouville_momentum_origin (-1) g (deriv g) hg.continuous
      (hg.continuous_deriv (by norm_num)))

end DefocusingNLS

end OAI
