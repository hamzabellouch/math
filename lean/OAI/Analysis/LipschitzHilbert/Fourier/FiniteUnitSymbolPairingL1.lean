import OAI.Analysis.LipschitzHilbert.Fourier.UnitConvolutionWeightL1
import OAI.Analysis.LipschitzHilbert.Fourier.UnitSymbolPairingL1

namespace OAI

/-! Exact Fourier separation of a finite sum before applying its model
estimate. All rows share the outside symbol parameter and its weight. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem unit_symbol_convolution_pairing_l1 (chi : SchwartzMap ℝ ℝ) (hchi : ∀ s, |chi s|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ)
    (A B : SchwartzMap (ℝ×ℝ) ℂ) (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) (U : ℝ×ℝ → ℝ) (hU : Measurable U)
    (g : ℝ×ℝ → ℂ) (hgm : Measurable g) (hg : Integrable g planeMeasure)
    (l W theta center : ℝ) :
    (∫ x, (chi (U x):ℂ)*
      (∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (S (symbolPoint (symbolX l omega.1 omega.2 theta)
          (symbolY W omega.2 center) (U x))*
            (A omega*B omega*planarFourier f omega)) ∂planeMeasure)*star (g x)
      ∂planeMeasure) =
    (selectorNormalizer chi C:ℂ)*(∫ nu : SymbolSpace, (symbolWeight q nu:ℂ)*
      ∫ x, unitPacketSelector chi C S q nu (U x)*
        kernelConvolution (horizontalFrequencyKernel A nu q l theta)
          (kernelConvolution (verticalFrequencyKernel B nu q W center) f) x*star (g x)
        ∂planeMeasure) := by
  have h := unit_symbol_pairing_l1 chi hchi C hC S q (packetFrequencyInputL1 A B f)
    (packetFrequencyInputL1_integrable A B f hf)
    U hU g hgm hg l W theta center
  simp only [packetFrequencyInputL1,starRingEnd_apply] at h
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with nu
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  have hk := frequencyKernel_convolution_l1 A B f hf nu q l W theta center x
  rw [←planarInverse_const_mul] at hk
  have he : (fun omega => (symbolWeight q nu:ℂ)^2*
      modulatedFrequency (packetFrequencyInputL1 A B f) nu l W theta center omega)=
      (fun omega => (symbolWeight q nu:ℂ)^2*
        modulatedFrequency (fun omega => A omega*B omega*planarFourier f omega)
          nu l W theta center omega) := by
    funext omega
    simp only [modulatedFrequency,packetFrequencyInputL1]
  rw [he] at hk
  rw [hk,he]

theorem finite_unit_symbol_pairing_l1 {ι : Type*} [Fintype ι]
    (chi : SchwartzMap ℝ ℝ) (hchi : ∀ s, |chi s|≤1) (C : ℝ) (hC : 0<C)
    (S : ι → SchwartzMap SymbolSpace ℂ) (q : ℕ) (hq : 4≤q)
    (hS : ∀ i, symbolCoefficientBound (S i) q≤C)
    (A B : ι → SchwartzMap (ℝ×ℝ) ℂ) (f : ι → ℝ×ℝ → ℂ)
    (hf : ∀ i, Integrable (f i) planeMeasure)
    (U : ι → ℝ×ℝ → ℝ) (hU : ∀ i, Measurable (U i))
    (g : ι → ℝ×ℝ → ℂ) (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, Integrable (g i) planeMeasure) (l W theta center : ι → ℝ) :
    (∑ i, ∫ x, (chi (U i x):ℂ)*
      (∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (S i (symbolPoint (symbolX (l i) omega.1 omega.2 (theta i))
          (symbolY (W i) omega.2 (center i)) (U i x))*
            (A i omega*B i omega*planarFourier (f i) omega)) ∂planeMeasure)*star (g i x)
      ∂planeMeasure) =
    (selectorNormalizer chi C:ℂ)*(∫ nu : SymbolSpace, (symbolWeight q nu:ℂ)*
      ∑ i, ∫ x, unitPacketSelector chi C (S i) q nu (U i x)*
        kernelConvolution (horizontalFrequencyKernel (A i) nu q (l i) (theta i))
          (kernelConvolution (verticalFrequencyKernel (B i) nu q (W i) (center i)) (f i)) x*
        star (g i x) ∂planeMeasure) := by
  let V := fun i nu => ∫ x, unitPacketSelector chi C (S i) q nu (U i x)*
    kernelConvolution (horizontalFrequencyKernel (A i) nu q (l i) (theta i))
      (kernelConvolution (verticalFrequencyKernel (B i) nu q (W i) (center i)) (f i)) x*
    star (g i x) ∂planeMeasure
  have hi (i : ι) : Integrable (fun nu => (symbolWeight q nu:ℂ)*V i nu) volume :=
    unitConvolution_weight_integrable_l1 chi hchi C hC (S i) q hq (hS i) (A i) (B i) (f i) (hf i)
      (U i) (hU i) (g i) (hgm i) (hg i) (l i) (W i) (theta i) (center i)
  calc
    _ = ∑ i, (selectorNormalizer chi C:ℂ)*(∫ nu : SymbolSpace, (symbolWeight q nu:ℂ)*V i nu) :=
      Finset.sum_congr rfl (fun i _ => unit_symbol_convolution_pairing_l1 chi hchi C hC (S i) q
        (A i) (B i) (f i) (hf i) (U i) (hU i) (g i) (hgm i) (hg i) (l i) (W i) (theta i) (center i))
    _ = (selectorNormalizer chi C:ℂ)*(∑ i, ∫ nu : SymbolSpace, (symbolWeight q nu:ℂ)*V i nu) :=
      (Finset.mul_sum _ _ _).symm
    _ = (selectorNormalizer chi C:ℂ)*(∫ nu : SymbolSpace, ∑ i, (symbolWeight q nu:ℂ)*V i nu) := by
      rw [integral_finsetSum _ (fun i _ => hi i)]
    _ = _ := by simp only [Finset.mul_sum,V]

end LipschitzHilbert.PacketRepresentation

end

end OAI
