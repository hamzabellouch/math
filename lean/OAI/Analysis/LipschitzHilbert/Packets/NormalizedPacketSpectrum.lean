import OAI.Analysis.LipschitzHilbert.Packets.NormalizedPacketProfiles
import OAI.Analysis.LipschitzHilbert.Estimates.ScaledWindowSpectrum
import OAI.Analysis.LipschitzHilbert.Packets.ConvolutionPacketSpectrum

namespace OAI

/-! Exact angular-frequency strips for the constructed packet profiles.
Both waves keep the same positive carrier; neither reflection nor the
Fourier separation enlarges their frequency support. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

private theorem angular_strip_of_cycles (A B l W theta center xi eta : ℝ)
    (h : |xi/(2*Real.pi)+theta*(eta/(2*Real.pi))| ≤ A/l ∧
      |eta/(2*Real.pi)-center| ≤ B/W) :
    |xi+theta*eta| ≤ (2*Real.pi*A)/l ∧
      |eta-2*Real.pi*center| ≤ (2*Real.pi*B)/W := by
  have hp : 0 < 2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  have h₁ : xi/(2*Real.pi)+theta*(eta/(2*Real.pi)) =
      (xi+theta*eta)/(2*Real.pi) := by ring
  have h₂ : eta/(2*Real.pi)-center = (eta-2*Real.pi*center)/(2*Real.pi) := by
    field_simp [Real.pi_ne_zero]
  rw [h₁, h₂, abs_div, abs_div, abs_of_pos hp] at h
  constructor
  · exact ((div_le_iff₀ hp).mp h.1).trans_eq (by ring)
  · exact ((div_le_iff₀ hp).mp h.2).trans_eq (by ring)

theorem horizontal_scaled_angular_support (chi : SchwartzMap (ℝ×ℝ) ℂ) (A B : ℝ)
    (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (nu : SymbolSpace) (q : ℕ) (l W theta center : ℝ) (hl : 0<l) (hW : 0<W)
    (xi eta : ℝ) (h : planarAngularFourier (horizontalFrequencyKernel
      (scaledFrequencyWindow (planarInverseSchwartz chi) l W theta (2*Real.pi*center) hl.ne' hW.ne')
        nu q l theta) (xi,eta)≠0) :
    |xi+theta*eta|≤(2*Real.pi*A)/l ∧ |eta-2*Real.pi*center|≤(2*Real.pi*B)/W := by
  exact angular_strip_of_cycles A B l W theta center xi eta
    (horizontal_scaled_kernel_support chi A B hchi nu q l W theta center hl hW
      (xi/(2*Real.pi)) (eta/(2*Real.pi)) h)

theorem vertical_scaled_angular_support (chi : SchwartzMap (ℝ×ℝ) ℂ) (A B : ℝ)
    (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (nu : SymbolSpace) (q : ℕ) (l W theta center : ℝ) (hl : 0<l) (hW : 0<W)
    (xi eta : ℝ) (h : planarAngularFourier (verticalFrequencyKernel
      (scaledFrequencyWindow (planarInverseSchwartz chi) l W theta (2*Real.pi*center) hl.ne' hW.ne')
        nu q W center) (xi,eta)≠0) :
    |xi+theta*eta|≤(2*Real.pi*A)/l ∧ |eta-2*Real.pi*center|≤(2*Real.pi*B)/W := by
  exact angular_strip_of_cycles A B l W theta center xi eta
    (vertical_scaled_kernel_support chi A B hchi nu q l W theta center hl hW
      (xi/(2*Real.pi)) (eta/(2*Real.pi)) h)

theorem synthesisProfile_angular_support (chi : SchwartzMap (ℝ×ℝ) ℂ) (A B : ℝ)
    (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (nu : SymbolSpace) (q : ℕ) (l W theta center : ℝ) (hl : 0<l) (hW : 0<W)
    (z : ℝ×ℝ) (xi eta : ℝ)
    (h : planarAngularFourier (physicalPlanarPacket
      (synthesisProfile (planarInverseSchwartz chi) q nu) z.1 z.2
        l W theta (2*Real.pi*center) hl.ne' hW.ne') (xi,eta)≠0) :
    |xi+theta*eta|≤(2*Real.pi*A)/l ∧ |eta-2*Real.pi*center|≤(2*Real.pi*B)/W := by
  have heq := funext (physical_synthesisProfile (planarInverseSchwartz chi) q nu
    l W theta center hl.ne' hW.ne' z)
  rw [heq] at h
  exact synthesisWave_spectrum (S := {p | |p.1+theta*p.2|≤(2*Real.pi*A)/l ∧
      |p.2-2*Real.pi*center|≤(2*Real.pi*B)/W}) (l*W) _
    (fun p hp => horizontal_scaled_angular_support chi A B hchi nu q l W theta center
      hl hW p.1 p.2 hp) z (xi,eta) h

theorem analysisProfile_angular_support (chi : SchwartzMap (ℝ×ℝ) ℂ) (A B : ℝ)
    (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (nu : SymbolSpace) (q : ℕ) (l W theta center : ℝ) (hl : 0<l) (hW : 0<W)
    (z : ℝ×ℝ) (xi eta : ℝ)
    (h : planarAngularFourier (physicalPlanarPacket
      (analysisProfile (planarInverseSchwartz chi) q nu) z.1 z.2
        l W theta (2*Real.pi*center) hl.ne' hW.ne') (xi,eta)≠0) :
    |xi+theta*eta|≤(2*Real.pi*A)/l ∧ |eta-2*Real.pi*center|≤(2*Real.pi*B)/W := by
  have heq := funext (physical_analysisProfile (planarInverseSchwartz chi) q nu
    l W theta center hl.ne' hW.ne' z)
  rw [heq] at h
  exact analyzingWave_spectrum (S := {p | |p.1+theta*p.2|≤(2*Real.pi*A)/l ∧
      |p.2-2*Real.pi*center|≤(2*Real.pi*B)/W}) (l*W) _
    (fun p hp => vertical_scaled_angular_support chi A B hchi nu q l W theta center
      hl hW p.1 p.2 hp) z (xi,eta) h

end LipschitzHilbert.PacketRepresentation

end

end OAI
