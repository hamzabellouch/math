import OAI.Analysis.LipschitzHilbert.Fourier.UnitSymbolPairing
import OAI.Analysis.LipschitzHilbert.Packets.PlanarFrequencyPackets

namespace OAI

/-! The localized frequency multiplier is exactly a weighted integral of
lattice packet forms, with the actual normalized selector and kernels. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate BigOperators
namespace LipschitzHilbert.PacketRepresentation

def packetFrequencyInput (A B f : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) A B) (planarFourierSchwartz f)

theorem packetFrequencyInput_apply (A B f : SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ) :
    packetFrequencyInput A B f omega = A omega*B omega*planarFourier f omega := by
  simp only [packetFrequencyInput,SchwartzMap.pairing_apply_apply,planarFourierSchwartz_apply]
  rfl

theorem separated_packet_form (chi : SchwartzMap ℝ ℝ) (hchi : ∀ s, |chi s|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ)
    (hS : symbolCoefficientBound S q≤C)
    (A B f : SchwartzMap (ℝ×ℝ) ℂ) (U : ℝ×ℝ → ℝ) (hU : Measurable U)
    (g : ℝ×ℝ → ℂ) (hgm : Measurable g) (hg : Integrable g planeMeasure)
    (Mg : ℝ) (hgb : ∀ x, ‖g x‖≤Mg)
    (l W theta center : ℝ) (hl : 0<l) (hW : 0<W) :
    (∫ x, (chi (U x):ℂ)*
      (∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (S (symbolPoint (symbolX l omega.1 omega.2 theta)
          (symbolY W omega.2 center) (U x))*
            (A omega*B omega*planarFourier f omega)) ∂planeMeasure)*conj (g x)
        ∂planeMeasure) =
    (selectorNormalizer chi C:ℂ)*(∫ nu : SymbolSpace, (symbolWeight q nu:ℂ)*
      ∫ z, ∑' n : ℤ×ℤ, ((l*W:ℝ):ℂ)⁻¹*
        packetProduct (horizontalFrequencyKernel A nu q l theta)
          (verticalFrequencyKernel B nu q W center) f
          (fun x => unitPacketSelector chi C S q nu (U x)) g (l*W)
          (latticeHom l W theta n+z) ∂latticeAverage l W theta) := by
  have hrepr := unit_symbol_pairing chi hchi C hC S q (packetFrequencyInput A B f)
    U hU g hgm hg l W theta center
  simp only [packetFrequencyInput_apply] at hrepr
  rw [hrepr]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with nu
  congr 1
  have hb : Measurable (fun x => unitPacketSelector chi C S q nu (U x)) :=
    (unitPacketSelector_differentiable chi C S q nu).continuous.measurable.comp hU
  have hbb : ∀ x, ‖unitPacketSelector chi C S q nu (U x)‖≤1 :=
    fun x => unitPacketSelector_bound chi hchi C hC S q hS nu (U x)
  have hfreq : (fun omega => (symbolWeight q nu:ℂ)^2*
      modulatedFrequency (packetFrequencyInput A B f) nu l W theta center omega) =
      (fun omega => (symbolWeight q nu:ℂ)^2*
        modulatedFrequency (fun omega => A omega*B omega) nu l W theta center omega*
          planarFourier f omega) := by
    funext omega
    rw [modulatedFrequency,modulatedFrequency,packetFrequencyInput_apply]
    ring
  rw [hfreq]
  exact frequencyKernel_packet_average A B f
    (fun x => unitPacketSelector chi C S q nu (U x)) g hb hgm 1 Mg hbb hgb
      nu q l W theta center hl hW

end LipschitzHilbert.PacketRepresentation

end

end OAI
