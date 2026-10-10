import OAI.Analysis.LipschitzHilbert.Fourier.VerticalSecantEnergy
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinEnergy
import OAI.Analysis.LipschitzHilbert.Fourier.PlanarSliceFourierDerivative

namespace OAI

/-! The vertical derivative bound used only on the actual finite frequency bins. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalSchwartzDeriv_eq (f : SchwartzMap (ℝ×ℝ) ℂ) :
    verticalSchwartzDeriv f=planarVerticalDerivative f := by
  ext z
  rfl

theorem verticalSchwartzDeriv_fourier (f : SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ) :
    planarFourier (verticalSchwartzDeriv f) omega=
      (2*Real.pi*Complex.I*omega.2)*planarFourier f omega := by
  rw [verticalSchwartzDeriv_eq]
  exact planarFourier_verticalDerivative f omega.1 omega.2

theorem vertical_bernstein_energy (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ) (_hR : 0≤R)
    (hband : ∀ omega, planarFourier f omega≠0 → |omega.2|≤R) :
    (∫ z, ‖verticalSchwartzDeriv f z‖^2 ∂planeMeasure)≤
      (2*Real.pi*R)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  have hi (g : SchwartzMap (ℝ×ℝ) ℂ) :
      Integrable (fun omega => ‖planarFourier g omega‖^2) planeMeasure := by
    simpa only [planarFourierSchwartz_apply] using
      ((planarFourierSchwartz g).memLp 2 planeMeasure).integrable_norm_pow (by decide : 2≠0)
  have hp (omega : ℝ×ℝ) : ‖planarFourier (verticalSchwartzDeriv f) omega‖^2≤
      (2*Real.pi*R)^2*‖planarFourier f omega‖^2 := by
    rw [verticalSchwartzDeriv_fourier,norm_mul]
    by_cases hf : planarFourier f omega=0
    · simp only [hf,norm_zero,mul_zero,zero_pow (by decide : 2≠0),le_refl]
    · have hc : ‖(2*Real.pi*Complex.I*omega.2 : ℂ)‖=2*Real.pi*|omega.2| := by
        simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
      rw [hc,mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul_of_nonneg_left (hband omega hf) (by positivity)
  calc
    _ = ∫ omega, ‖planarFourier (verticalSchwartzDeriv f) omega‖^2 ∂planeMeasure :=
      (planar_integral_norm_sq_fourier _).symm
    _ ≤ ∫ omega, (2*Real.pi*R)^2*‖planarFourier f omega‖^2 ∂planeMeasure :=
      integral_mono (hi _) ((hi f).const_mul _) hp
    _ = _ := by rw [integral_const_mul,planar_integral_norm_sq_fourier]

end LipschitzHilbert.PacketRepresentation

end

end OAI
