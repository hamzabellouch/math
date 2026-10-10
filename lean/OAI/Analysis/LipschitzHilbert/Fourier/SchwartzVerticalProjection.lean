import OAI.Analysis.LipschitzHilbert.Fourier.VerticalInverseMultiplier

namespace OAI

/-! Vertical frequency cutoffs preserve the actual planar Schwartz class. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem verticalProfile_temperate (q : SchwartzMap ℝ ℂ) (W center : ℝ) :
    Function.HasTemperateGrowth (fun omega : ℝ×ℝ => q (W*(omega.2-center))) := by
  have hs : Function.HasTemperateGrowth (fun omega : ℝ×ℝ => omega.2) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasTemperateGrowth
  exact q.hasTemperateGrowth.comp (by fun_prop)

def schwartzVerticalProjection (q : SchwartzMap ℝ ℂ) (W center : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  planarInverseSchwartz (SchwartzMap.smulLeftCLM ℂ
    (fun omega : ℝ×ℝ => q (W*(omega.2-center))) (planarFourierSchwartz f))

theorem schwartzVerticalProjection_fourier (q : SchwartzMap ℝ ℂ) (W center : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ) :
    planarFourier (schwartzVerticalProjection q W center f) omega=
      q (W*(omega.2-center))*planarFourier f omega := by
  rw [schwartzVerticalProjection,planarInverseSchwartz_fourier,
    SchwartzMap.smulLeftCLM_apply_apply (verticalProfile_temperate q W center),
    planarFourierSchwartz_apply,smul_eq_mul]

theorem schwartzVerticalProjection_eq_convolution (q : SchwartzMap ℝ ℂ) (W center : ℝ)
    (hW : 0<W) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    schwartzVerticalProjection q W center f z=
      verticalConvolution (verticalProfileKernel q W center) f z := by
  rw [schwartz_vertical_multiplier (verticalProfileKernel q W center)
    (modulatedTimeKernel_integrable (𝓕⁻ q : SchwartzMap ℝ ℂ) W center hW)]
  simp_rw [verticalProfileKernel_fourier q W center _ hW]
  rw [schwartzVerticalProjection,planarInverseSchwartz_apply]
  congr 1
  funext omega
  rw [SchwartzMap.smulLeftCLM_apply_apply (verticalProfile_temperate q W center),
    planarFourierSchwartz_apply,smul_eq_mul]

theorem planar_schwartz_ext_fourier (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (h : ∀ omega, planarFourier f omega=planarFourier g omega) : f=g := by
  ext z
  rw [←planarFourier_inversion f z,←planarFourier_inversion g z]
  exact congrArg (fun F => planarInverse F z) (funext h)

end LipschitzHilbert.PacketRepresentation

end

end OAI
