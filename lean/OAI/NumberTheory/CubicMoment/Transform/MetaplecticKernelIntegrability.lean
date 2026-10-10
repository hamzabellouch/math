import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTransformContour
import OAI.NumberTheory.CubicMoment.Estimates.GammaQuotientGrowth

namespace OAI

/-! Absolute convergence of the literal metaplectic Mellin kernel, derived
from the proved Gamma strip bound and the smooth weight's rapid decay. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem metaplecticKernel_integrable (ℓ : ℤ) (W : ℝ→ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {a v : ℝ} (ha : a ≤ 1/2) (hv : 0<v) :
    Integrable (fun t : ℝ => (v:ℂ)^(a+(t:ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ (a+(t:ℂ)*Complex.I)*
        mellin W (a+(t:ℂ)*Complex.I)) := by
  have hstrip := min_le_left a (1/2:ℝ)
  obtain ⟨C,N,hC,hQ⟩ := metaplecticGamma_strip_bound ℓ (min a (1/2))
    (angularGammaQuotientStripBound_proved _ _ (by linarith [metaplecticAngularShift_nonneg ℓ]))
    (angularGammaQuotientStripBound_proved _ _ (by linarith [metaplecticAngularShift_nonneg ℓ]))
  obtain ⟨Cw,hCw,hw⟩ := smooth_mellin_vertical_decay W hW hpos hsm a (N+2)
  have hg : Continuous (fun t : ℝ => metaplecticGammaQuotient ℓ (a+(t:ℂ)*Complex.I)) :=
    (differentiableOn_metaplecticGammaQuotient ℓ).continuousOn.comp_continuous
      (by fun_prop) (by intro t; change (a+(t:ℂ)*Complex.I).re<5/6; simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]; linarith)
  have : NeZero (v:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hv.ne'⟩
  have hc : Continuous (fun t : ℝ => (v:ℂ)^(a+(t:ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ (a+(t:ℂ)*Complex.I)*mellin W (a+(t:ℂ)*Complex.I)) :=
    (((differentiable_const_cpow_of_neZero _).continuous.comp (by fun_prop)).mul hg).mul
      ((smooth_mellin_entire W hW hpos hsm.continuous).continuous.comp (by fun_prop))
  apply (mellinEdgeMajorant_integrable (v^a*C*Cw)).mono' hc.aestronglyMeasurable
  filter_upwards with t
  rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hv]
  have hr : (a+(t:ℂ)*Complex.I).re=a := by simp
  rw [hr]
  apply (le_div_iff₀ (by positivity : 0<(1+|t|)^2)).mpr
  calc
    _ ≤ (v^a*(C*(1+|t|)^N)*‖mellin W (a+(t:ℂ)*Complex.I)‖)*(1+|t|)^2 := by
      gcongr
      exact hQ a ⟨hstrip,ha⟩ t
    _ = (v^a*C)*((1+|t|)^(N+2)*‖mellin W (a+(t:ℂ)*Complex.I)‖) := by
      rw [pow_add]
      ring
    _ ≤ (v^a*C)*Cw := mul_le_mul_of_nonneg_left (hw t) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
