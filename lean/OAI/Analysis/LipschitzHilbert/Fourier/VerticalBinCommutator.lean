import OAI.Analysis.LipschitzHilbert.Fourier.VerticalCommutatorEnergy
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBernstein

namespace OAI

/-! The actual bin commutator on a vertical frequency band. Its constant
depends only on the fixed profile; its scale dependence is `t² (W R)²`. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def verticalProfileCommutatorConstant (q : SchwartzMap ℝ ℂ) : ℝ :=
  16*(2*Real.pi)^2*(∫ s, ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) s‖)*
    (∫ s, s^2*‖(𝓕⁻ q : SchwartzMap ℝ ℂ) s‖)

theorem verticalProfileCommutatorConstant_nonneg (q : SchwartzMap ℝ ℂ) :
    0≤verticalProfileCommutatorConstant q := by
  unfold verticalProfileCommutatorConstant
  positivity

theorem verticalProfileCommutator_energy (q : SchwartzMap ℝ ℂ)
    (W center : ℝ) (hW : 0<W) (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (t : ℝ) (ht : |t|≤1/4) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (R : ℝ) (hR : 0≤R)
    (hband : ∀ omega, planarFourier f omega≠0 → |omega.2|≤R) :
    MemLp (verticalSamplingCommutator (verticalProfileKernel q W center) u t f)
      2 planeMeasure ∧
    (∫ z, ‖verticalSamplingCommutator (verticalProfileKernel q W center) u t f z‖^2
        ∂planeMeasure)≤
      verticalProfileCommutatorConstant q*t^2*(W*R)^2*
        (∫ z, ‖f z‖^2 ∂planeMeasure) := by
  have hK := modulatedTimeKernel_integrable (𝓕⁻ q) W center hW
  have hKm : Measurable (verticalProfileKernel q W center) := by
    unfold verticalProfileKernel modulatedTimeKernel scaledTimeKernel
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (continuous_const.mul ((𝓕⁻ q : SchwartzMap ℝ ℂ).continuous.comp
        (by fun_prop)))).measurable
  obtain ⟨hmem,henergy⟩ := verticalSamplingCommutator_energy
    (verticalProfileKernel q W center) hKm hK
    (modulatedTimeKernel_moment2_integrable (𝓕⁻ q) W center hW) u hu t ht f
  refine ⟨hmem, henergy.trans ?_⟩
  have hcoeff : 0≤16*t^2*(∫ s, ‖verticalProfileKernel q W center s‖)*
      (∫ s, s^2*‖verticalProfileKernel q W center s‖) := by positivity
  calc
    _ ≤ (16*t^2*(∫ s, ‖verticalProfileKernel q W center s‖)*
        (∫ s, s^2*‖verticalProfileKernel q W center s‖))*
        ((2*Real.pi*R)^2*(∫ z, ‖f z‖^2 ∂planeMeasure)) :=
      mul_le_mul_of_nonneg_left (vertical_bernstein_energy f R hR hband) hcoeff
    _ = _ := by
      unfold verticalProfileKernel
      rw [modulatedTimeKernel_l1 _ W center hW,modulatedTimeKernel_moment2 _ W center hW]
      unfold verticalProfileCommutatorConstant
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
