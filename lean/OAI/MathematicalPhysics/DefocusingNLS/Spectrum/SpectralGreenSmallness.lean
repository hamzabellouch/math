import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGreenIntegralBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCouplingEstimate

namespace OAI

/-! The Green correction is small by the precise factor 1/(R kappa²),
where kappa is the lower bound for the square-root frequency weight. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralScalarGreenIntegral_small
    (R E r k kap A C M : ℝ) (hR : 0<R) (hr : r ∈ Icc R E)
    (hk : 0≤ k) (hkap : 0<kap) (hA : 0≤ A) (hC : 0≤ C) (hM : 0≤ M)
    (D U : ℝ → ℂ × ℂ) (W : ℂ) (f : ℝ → ℂ)
    (hD : ContinuousOn D (Icc R E)) (hU : ContinuousOn U (Icc R E))
    (hf : ContinuousOn f (Icc R E))
    (hleft : ∀ t ∈ Icc R r, spectralShellNorm k (((D t).1/W) • U r)≤ A/kap)
    (hright : ∀ t ∈ Icc r E, spectralShellNorm k (((U t).1/W) • D r)≤ A/kap)
    (hforcing : ∀ t ∈ Icc R E, ‖f t‖≤ C/(kap*t^2)*M) :
    spectralShellNorm k (spectralScalarGreenIntegral R E D U W f r)≤
      A*C*M/(kap^2*R) := by
  have hRE : R≤ E := hr.1.trans hr.2
  have hb := spectralScalarGreenIntegral_shell_bound R E r k hr hk D U W f
    (fun _ => A/kap) hD hU hf continuousOn_const hleft hright
  let B := A*C*M/kap^2
  have hB : 0≤ B := by dsimp only [B]; positivity
  have hi : ContinuousOn (fun t : ℝ => B*(t^2)⁻¹) (Icc R E) :=
    continuousOn_const.mul ((continuousOn_id.pow 2).inv₀
      (fun t ht => pow_ne_zero _ (ne_of_gt (hR.trans_le ht.1))))
  have hm : (∫ t in R..E, A/kap*‖f t‖)≤∫ t in R..E, B*(t^2)⁻¹ := by
    apply intervalIntegral.integral_mono_on hRE
      (ContinuousOn.intervalIntegrable_of_Icc hRE (continuousOn_const.mul hf.norm))
      (ContinuousOn.intervalIntegrable_of_Icc hRE hi)
    intro t ht
    calc
      _ ≤ A/kap*(C/(kap*t^2)*M) :=
        mul_le_mul_of_nonneg_left (hforcing t ht) (div_nonneg hA hkap.le)
      _ = _ := by dsimp only [B]; ring
  calc
    _ ≤ ∫ t in R..E, B*(t^2)⁻¹ := hb.trans hm
    _ = B*(∫ t in R..E, (t^2)⁻¹) := intervalIntegral.integral_const_mul _ _
    _ ≤ B*R⁻¹ := mul_le_mul_of_nonneg_left (spectral_inverse_square_integral_le R E hR hRE) hB
    _ = _ := by dsimp only [B]; ring

end DefocusingNLS

end OAI
