import OAI.Analysis.LipschitzHilbert.Fourier.LineFrequencyProjection
import OAI.Analysis.LipschitzHilbert.Fourier.FourierKernelFirstMoment

namespace OAI

/-! Differentiation commutes with the actual smooth line projections,
and a compact Fourier band gives the required Bernstein energy bound. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProjection_derivative (q : SchwartzMap ℝ ℂ)
    (W : ℝ) (hW : W≠0) (f : SchwartzMap ℝ ℂ) :
    schwartzDerivative 1 (lineSchwartzProjection q W hW f)=
      lineSchwartzProjection q W hW (schwartzDerivative 1 f) := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (schwartzDerivative 1 (lineSchwartzProjection q W hW f))) eta=
    (𝓕 (lineSchwartzProjection q W hW (schwartzDerivative 1 f))) eta
  rw [fourier_schwartzDerivative,lineSchwartzProjection_fourier,
    lineSchwartzProjection_fourier,fourier_schwartzDerivative]
  ring

theorem line_bernstein_energy (f : SchwartzMap ℝ ℂ) (R : ℝ)
    (hband : ∀ eta, (𝓕 f : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤R) :
    (∫ x, ‖schwartzDerivative 1 f x‖^2)≤(2*Real.pi*R)^2*(∫ x, ‖f x‖^2) := by
  have hi (g : SchwartzMap ℝ ℂ) : Integrable (fun eta => ‖(𝓕 g : SchwartzMap ℝ ℂ) eta‖^2) :=
    ((𝓕 g : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  have hp (eta : ℝ) : ‖(𝓕 (schwartzDerivative 1 f) : SchwartzMap ℝ ℂ) eta‖^2≤
      (2*Real.pi*R)^2*‖(𝓕 f : SchwartzMap ℝ ℂ) eta‖^2 := by
    rw [fourier_schwartzDerivative 1 f eta,pow_one,norm_mul]
    by_cases hf : (𝓕 f : SchwartzMap ℝ ℂ) eta=0
    · simp only [hf,norm_zero,mul_zero,zero_pow (by decide : 2≠0),le_refl]
    · have hc : ‖(2*Real.pi*Complex.I*(eta:ℂ))‖=2*Real.pi*|eta| := by
        simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
      rw [hc,mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left (hband eta hf) (by positivity)) 2
  calc
    _ = ∫ eta, ‖(𝓕 (schwartzDerivative 1 f) : SchwartzMap ℝ ℂ) eta‖^2 := (SchwartzMap.integral_norm_sq_fourier (schwartzDerivative 1 f)).symm
    _ ≤ ∫ eta, (2*Real.pi*R)^2*‖(𝓕 f : SchwartzMap ℝ ℂ) eta‖^2 := integral_mono (hi _) ((hi f).const_mul _) hp
    _ = _ := by rw [integral_const_mul,SchwartzMap.integral_norm_sq_fourier f]

end LipschitzHilbert.PacketRepresentation

end

end OAI
