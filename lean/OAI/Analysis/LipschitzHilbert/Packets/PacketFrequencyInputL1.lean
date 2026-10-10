import OAI.Analysis.LipschitzHilbert.Fourier.L1FactoredConvolution
import OAI.Analysis.LipschitzHilbert.Fourier.ModulatedInverseL1
import OAI.Analysis.LipschitzHilbert.Fourier.UnitConvolutionParameter

namespace OAI

/-! Frequency input and exact separated convolution identities for L1
data, including the amplitude slices of the bin decomposition. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def packetFrequencyInputL1 (A B : SchwartzMap (ℝ×ℝ) ℂ) (f : ℝ×ℝ → ℂ) : ℝ×ℝ → ℂ :=
  fun omega => A omega*B omega*planarFourier f omega

theorem packetFrequencyInputL1_integrable (A B : SchwartzMap (ℝ×ℝ) ℂ)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) :
    Integrable (packetFrequencyInputL1 A B f) planeMeasure := by
  have hAB : Integrable (fun omega => A omega*B omega) planeMeasure :=
    A.integrable.mul_bdd B.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun omega => SchwartzMap.norm_le_seminorm ℝ B omega))
  exact hAB.mul_bdd (planarFourier_l1_continuous f hf).aestronglyMeasurable
    (Filter.Eventually.of_forall (planarFourier_l1_bound f))

theorem frequencyKernel_convolution_l1 (A B : SchwartzMap (ℝ×ℝ) ℂ)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure)
    (nu : SymbolSpace) (q : ℕ) (l W theta center : ℝ) (x : ℝ×ℝ) :
    kernelConvolution (horizontalFrequencyKernel A nu q l theta)
      (kernelConvolution (verticalFrequencyKernel B nu q W center) f) x=
    (symbolWeight q nu:ℂ)^2*
      planarInverse (modulatedFrequency (packetFrequencyInputL1 A B f) nu l W theta center) x := by
  rw [←factored_multiplier_convolution_l1 _ _ f hf]
  simp_rw [frequencyKernel_product]
  rw [←planarInverse_const_mul]
  congr 1
  funext omega
  unfold modulatedFrequency packetFrequencyInputL1
  ring

theorem frequencyKernel_convolution_joint_continuous_l1 (A B : SchwartzMap (ℝ×ℝ) ℂ)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure)
    (q : ℕ) (l W theta center : ℝ) :
    Continuous (fun p : SymbolSpace×(ℝ×ℝ) =>
      kernelConvolution (horizontalFrequencyKernel A p.1 q l theta)
        (kernelConvolution (verticalFrequencyKernel B p.1 q W center) f) p.2) := by
  simp_rw [frequencyKernel_convolution_l1 A B f hf]
  exact ((Complex.continuous_ofReal.comp ((symbolWeight_continuous q).comp continuous_fst)).pow 2).mul
    (modulated_inverse_joint_continuous_l1 (packetFrequencyInputL1 A B f)
      (packetFrequencyInputL1_integrable A B f hf) l W theta center)

theorem unitConvolution_pairing_stronglyMeasurable_l1 (chi : SchwartzMap ℝ ℝ) (C : ℝ)
    (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (A B : SchwartzMap (ℝ×ℝ) ℂ)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure)
    (U : ℝ×ℝ → ℝ) (hU : Measurable U)
    (g : ℝ×ℝ → ℂ) (hg : Measurable g) (l W theta center : ℝ) :
    StronglyMeasurable (fun nu : SymbolSpace => ∫ x,
      unitPacketSelector chi C S q nu (U x)*
        kernelConvolution (horizontalFrequencyKernel A nu q l theta)
          (kernelConvolution (verticalFrequencyKernel B nu q W center) f) x*
        star (g x) ∂planeMeasure) := by
  have hsel : Measurable (fun p : SymbolSpace×(ℝ×ℝ) =>
      unitPacketSelector chi C S q p.1 (U p.2)) :=
    (unitPacketSelector_joint_continuous chi C S q).measurable.comp
      (measurable_fst.prodMk (hU.comp measurable_snd))
  have hker := (frequencyKernel_convolution_joint_continuous_l1 A B f hf q l W theta center).measurable
  have htest : Measurable (fun p : SymbolSpace×(ℝ×ℝ) => star (g p.2)) :=
    continuous_star.measurable.comp (hg.comp measurable_snd)
  exact ((hsel.mul hker).mul htest).stronglyMeasurable.integral_prod_right'

end LipschitzHilbert.PacketRepresentation

end

end OAI
