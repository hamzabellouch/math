import OAI.Analysis.LipschitzHilbert.Fourier.LineKernelScaling

namespace OAI

/-! Fixed zeroth and second decay bounds for the scaled line kernel. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def lineKernelDecayConstant (q : SchwartzMap ℝ ℂ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 (𝓕⁻ q)+SchwartzMap.seminorm ℝ 2 0 (𝓕⁻ q)

theorem lineKernelDecayConstant_nonneg (q : SchwartzMap ℝ ℂ) : 0≤lineKernelDecayConstant q :=
  add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)

theorem lineKernelDecay_base (q : SchwartzMap ℝ ℂ) (t : ℝ) :
    ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖≤lineKernelDecayConstant q ∧
    |t|^2*‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖≤lineKernelDecayConstant q := by
  constructor
  · exact ((𝓕⁻ q : SchwartzMap ℝ ℂ).norm_le_seminorm ℝ t).trans
      (le_add_of_nonneg_right (apply_nonneg _ _))
  · have h := (𝓕⁻ q : SchwartzMap ℝ ℂ).norm_pow_mul_le_seminorm ℝ 2 t
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_add_of_nonneg_left (apply_nonneg _ _))

theorem lineProjectionKernel_norm (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) (t : ℝ) :
    ‖lineProjectionKernel q W hW.ne' t‖=W⁻¹*‖(𝓕⁻ q : SchwartzMap ℝ ℂ) (t/W)‖ := by
  rw [lineProjectionKernel_eq_scaled q W hW,scaledSchwartzKernel_apply q W hW]
  simp only [scaledTimeKernel,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hW.le]

theorem lineProjectionKernel_decay (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) (t : ℝ) :
    ‖lineProjectionKernel q W hW.ne' t‖≤lineKernelDecayConstant q/W ∧
    |t|^2*‖lineProjectionKernel q W hW.ne' t‖≤lineKernelDecayConstant q*W := by
  rw [lineProjectionKernel_norm q W hW t]
  constructor
  · simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left
      (lineKernelDecay_base q (t/W)).1 (inv_nonneg.mpr hW.le)
  · have h := mul_le_mul_of_nonneg_right (lineKernelDecay_base q (t/W)).2 hW.le
    rw [abs_div,abs_of_pos hW] at h
    convert h using 1; field_simp

end LipschitzHilbert.PacketRepresentation

end

end OAI
