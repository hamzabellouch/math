import OAI.Analysis.LipschitzHilbert.Packets.SeparatedPacketForm
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! Joint dependence on the remaining Fourier parameter. These are the
literal kernels and selectors in the packet representation, so their
finite sums may be integrated against the outside symbol weight. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem symbolWeight_continuous (q : ℕ) : Continuous (symbolWeight q) := by
  unfold symbolWeight
  exact ((continuous_const.add continuous_norm).pow q).inv₀
    (fun nu => (pow_pos (by positivity : 0<1+‖nu‖) q).ne')

theorem unitPacketSelector_joint_continuous (chi : SchwartzMap ℝ ℝ) (C : ℝ)
    (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) :
    Continuous (fun p : SymbolSpace×ℝ => unitPacketSelector chi C S q p.1 p.2) := by
  have hw : ∀ p : SymbolSpace×ℝ, ((symbolWeight q p.1:ℝ):ℂ)^3≠0 := by
    intro p
    apply pow_ne_zero
    exact_mod_cast (symbolWeight_pos q p.1).ne'
  have hs : Continuous (fun p : SymbolSpace×ℝ => selectorCharacter p.1 p.2) := by
    unfold selectorCharacter
    fun_prop
  unfold unitPacketSelector localizedSelector weightedSelector
  exact continuous_const.mul ((Complex.continuous_ofReal.comp (chi.continuous.comp continuous_snd)).mul
    ((((𝓕 S : SchwartzMap SymbolSpace ℂ).continuous.comp continuous_fst).div
      ((Complex.continuous_ofReal.comp ((symbolWeight_continuous q).comp continuous_fst)).pow 3) hw).mul hs))

theorem frequencyKernel_convolution (A B f : SchwartzMap (ℝ×ℝ) ℂ)
    (nu : SymbolSpace) (q : ℕ) (l W theta center : ℝ) (x : ℝ×ℝ) :
    kernelConvolution (horizontalFrequencyKernel A nu q l theta)
      (kernelConvolution (verticalFrequencyKernel B nu q W center) f) x=
    (symbolWeight q nu:ℂ)^2*
      planarInverse (modulatedFrequency (packetFrequencyInput A B f) nu l W theta center) x := by
  rw [←factored_multiplier_convolution]
  simp_rw [frequencyKernel_product]
  rw [←planarInverse_const_mul]
  congr 1
  funext omega
  unfold modulatedFrequency
  rw [packetFrequencyInput_apply]
  ring

theorem frequencyKernel_convolution_joint_continuous (A B f : SchwartzMap (ℝ×ℝ) ℂ)
    (q : ℕ) (l W theta center : ℝ) :
    Continuous (fun p : SymbolSpace×(ℝ×ℝ) =>
      kernelConvolution (horizontalFrequencyKernel A p.1 q l theta)
        (kernelConvolution (verticalFrequencyKernel B p.1 q W center) f) p.2) := by
  simp_rw [frequencyKernel_convolution]
  exact ((Complex.continuous_ofReal.comp ((symbolWeight_continuous q).comp continuous_fst)).pow 2).mul
    (modulated_inverse_joint_continuous (packetFrequencyInput A B f) l W theta center)

theorem unitConvolution_pairing_stronglyMeasurable (chi : SchwartzMap ℝ ℝ) (C : ℝ)
    (S : SchwartzMap SymbolSpace ℂ) (q : ℕ)
    (A B f : SchwartzMap (ℝ×ℝ) ℂ) (U : ℝ×ℝ → ℝ) (hU : Measurable U)
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
  have hker := (frequencyKernel_convolution_joint_continuous A B f q l W theta center).measurable
  have htest : Measurable (fun p : SymbolSpace×(ℝ×ℝ) => star (g p.2)) :=
    continuous_star.measurable.comp (hg.comp measurable_snd)
  exact ((hsel.mul hker).mul htest).stronglyMeasurable.integral_prod_right'

end LipschitzHilbert.PacketRepresentation

end

end OAI
