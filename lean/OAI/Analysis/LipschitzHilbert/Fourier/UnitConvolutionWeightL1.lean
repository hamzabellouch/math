import OAI.Analysis.LipschitzHilbert.Packets.PacketFrequencyInputL1
import OAI.Analysis.LipschitzHilbert.Fourier.SymbolAverageBound

namespace OAI

/-! An integrable majorant justifying the outside Fourier integral.
This bound is used only for interchanging finite sums and integration;
the uniform model bounds are applied to their complete joint sum. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem unitConvolution_pairing_bound_l1 (chi : SchwartzMap ℝ ℝ) (hchi : ∀ s, |chi s|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ)
    (hS : symbolCoefficientBound S q≤C)
    (A B : SchwartzMap (ℝ×ℝ) ℂ) (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) (U : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → ℂ) (hg : Integrable g planeMeasure)
    (l W theta center : ℝ) (nu : SymbolSpace) :
    ‖∫ x, unitPacketSelector chi C S q nu (U x)*
      kernelConvolution (horizontalFrequencyKernel A nu q l theta)
        (kernelConvolution (verticalFrequencyKernel B nu q W center) f) x*
      star (g x) ∂planeMeasure‖≤
        (∫ omega, ‖packetFrequencyInputL1 A B f omega‖ ∂planeMeasure)*(∫ x, ‖g x‖ ∂planeMeasure) := by
  let M := ∫ omega, ‖packetFrequencyInputL1 A B f omega‖ ∂planeMeasure
  have hkernel (x : ℝ×ℝ) :
      ‖kernelConvolution (horizontalFrequencyKernel A nu q l theta)
        (kernelConvolution (verticalFrequencyKernel B nu q W center) f) x‖≤M := by
    rw [frequencyKernel_convolution_l1 A B f hf,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (symbolWeight_pos q nu)]
    have hw : (symbolWeight q nu)^2≤1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (symbolWeight_pos q nu).le (symbolWeight_le_one q nu) 2
    exact (mul_le_mul hw (modulated_inverse_norm_le (packetFrequencyInputL1 A B f) nu l W theta center x)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul M)
  have hnorm (x : ℝ×ℝ) :
      ‖unitPacketSelector chi C S q nu (U x)*
        kernelConvolution (horizontalFrequencyKernel A nu q l theta)
          (kernelConvolution (verticalFrequencyKernel B nu q W center) f) x*star (g x)‖≤‖g x‖*M := by
    rw [norm_mul,norm_mul,norm_star]
    have hs := unitPacketSelector_bound chi hchi C hC S q hS nu (U x)
    calc
      _ ≤ (1*M)*‖g x‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul hs (hkernel x) (norm_nonneg _) (by norm_num)) (norm_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ∫ x, ‖g x‖*M ∂planeMeasure := norm_integral_le_of_norm_le (hg.norm.mul_const M)
      (Filter.Eventually.of_forall hnorm)
    _ = _ := by rw [integral_mul_const]; ring

theorem unitConvolution_weight_integrable_l1 (chi : SchwartzMap ℝ ℝ) (hchi : ∀ s, |chi s|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (hq : 4≤q)
    (hS : symbolCoefficientBound S q≤C)
    (A B : SchwartzMap (ℝ×ℝ) ℂ) (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) (U : ℝ×ℝ → ℝ) (hU : Measurable U)
    (g : ℝ×ℝ → ℂ) (hgm : Measurable g) (hg : Integrable g planeMeasure)
    (l W theta center : ℝ) :
    Integrable (fun nu : SymbolSpace => (symbolWeight q nu:ℂ)*∫ x,
      unitPacketSelector chi C S q nu (U x)*
        kernelConvolution (horizontalFrequencyKernel A nu q l theta)
          (kernelConvolution (verticalFrequencyKernel B nu q W center) f) x*
        star (g x) ∂planeMeasure) :=
  (symbol_average_bound q hq _
    (unitConvolution_pairing_stronglyMeasurable_l1 chi C S q A B f hf U hU g hgm l W theta center).aestronglyMeasurable
    _ (Filter.Eventually.of_forall (fun nu =>
      unitConvolution_pairing_bound_l1 chi hchi C hC S q hS A B f hf U g hg l W theta center nu))).1

end LipschitzHilbert.PacketRepresentation

end

end OAI
