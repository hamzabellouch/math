import OAI.Analysis.LipschitzHilbert.Fourier.FiniteUnitSymbolPairingL1

namespace OAI

/-! Apply the outside Fourier weight to the whole finite convolution
sum. The number of rows never appears in the transferred bound. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem finite_unit_convolution_average_bound_l1 {ι : Type*} [Fintype ι]
    (chi : SchwartzMap ℝ ℝ) (C : ℝ) (hC : 0<C)
    (S : ι → SchwartzMap SymbolSpace ℂ) (q : ℕ) (hq : 4≤q)
    (A B : ι → SchwartzMap (ℝ×ℝ) ℂ) (f : ι → ℝ×ℝ → ℂ)
    (hf : ∀ i, Integrable (f i) planeMeasure)
    (U : ι → ℝ×ℝ → ℝ) (hU : ∀ i, Measurable (U i))
    (g : ι → ℝ×ℝ → ℂ) (hgm : ∀ i, Measurable (g i)) (l W theta center : ι → ℝ)
    (bound : ℝ) :
    let V := fun i nu => ∫ x, unitPacketSelector chi C (S i) q nu (U i x)*
      kernelConvolution (horizontalFrequencyKernel (A i) nu q (l i) (theta i))
        (kernelConvolution (verticalFrequencyKernel (B i) nu q (W i) (center i)) (f i)) x*
      star (g i x) ∂planeMeasure
    (∀ nu : SymbolSpace, ‖∑ i, V i nu‖≤bound) →
    ‖(selectorNormalizer chi C:ℂ)*(∫ nu : SymbolSpace,
      (symbolWeight q nu:ℂ)*(∑ i, V i nu))‖≤
        selectorNormalizer chi C*bound*(∫ nu : SymbolSpace, symbolWeight q nu) := by
  intro V hbound
  have hm : StronglyMeasurable (fun nu : SymbolSpace => ∑ i, V i nu) :=
    Finset.stronglyMeasurable_fun_sum Finset.univ (fun i _ =>
      unitConvolution_pairing_stronglyMeasurable_l1 chi C (S i) q (A i) (B i) (f i) (hf i)
        (U i) (hU i) (g i) (hgm i) (l i) (W i) (theta i) (center i))
  have h := symbol_average_bound q hq _ hm.aestronglyMeasurable bound
    (Filter.Eventually.of_forall hbound)
  have hpos := selectorNormalizer_pos chi C hC
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpos]
  exact (mul_le_mul_of_nonneg_left h.2 hpos.le).trans_eq (by ring)

end LipschitzHilbert.PacketRepresentation

end

end OAI
