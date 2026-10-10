import OAI.Analysis.LipschitzHilbert.Estimates.FiniteUnitAverageL1

namespace OAI

/-! Transfer a uniform bound on the complete separated convolution sum
to the original finite symbol pairing. The two exact interchanges are
already proved, so no sum of individual row bounds is introduced. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem finite_separated_symbol_bound_l1 {ι : Type*} [Fintype ι]
    (chi : SchwartzMap ℝ ℝ) (hchi : ∀ s, |chi s|≤1) (C : ℝ) (hC : 0<C)
    (S : ι → SchwartzMap SymbolSpace ℂ) (q : ℕ) (hq : 4≤q)
    (hS : ∀ i, symbolCoefficientBound (S i) q≤C)
    (A B : ι → SchwartzMap (ℝ×ℝ) ℂ) (f : ι → ℝ×ℝ → ℂ)
    (hf : ∀ i, Integrable (f i) planeMeasure)
    (U : ι → ℝ×ℝ → ℝ) (hU : ∀ i, Measurable (U i))
    (g : ι → ℝ×ℝ → ℂ) (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, Integrable (g i) planeMeasure) (l W theta center : ι → ℝ)
    (bound : ℝ)
    (hbound : ∀ nu : SymbolSpace,
      ‖∑ i, ∫ x, unitPacketSelector chi C (S i) q nu (U i x)*
        kernelConvolution (horizontalFrequencyKernel (A i) nu q (l i) (theta i))
          (kernelConvolution (verticalFrequencyKernel (B i) nu q (W i) (center i)) (f i)) x*
          star (g i x) ∂planeMeasure‖≤bound) :
    ‖∑ i, ∫ x, (chi (U i x):ℂ)*
      (∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (S i (symbolPoint (symbolX (l i) omega.1 omega.2 (theta i))
          (symbolY (W i) omega.2 (center i)) (U i x))*
            (A i omega*B i omega*planarFourier (f i) omega)) ∂planeMeasure)*star (g i x)
      ∂planeMeasure‖≤selectorNormalizer chi C*bound*(∫ nu : SymbolSpace, symbolWeight q nu) := by
  rw [finite_unit_symbol_pairing_l1 chi hchi C hC S q hq hS A B f hf U hU g hgm hg l W theta center]
  exact finite_unit_convolution_average_bound_l1 chi C hC S q hq A B f hf U hU g hgm
    l W theta center bound hbound

end LipschitzHilbert.PacketRepresentation

end

end OAI
