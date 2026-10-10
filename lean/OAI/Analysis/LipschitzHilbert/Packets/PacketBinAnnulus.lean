import OAI.Analysis.LipschitzHilbert.Packets.NormalizedPacketSpectrum

namespace OAI

/-! Narrow bin support implies the common positive vertical annulus.
The loss depends on w/W, not on the number of bins. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem bin_support_annulus (w W center radius cEta CEta eta : ℝ)
    (hw : 0<w) (_hW : 0<W)
    (hlo : cEta + radius*(w/W) ≤ w*center)
    (hhi : w*center + radius*(w/W) ≤ CEta)
    (hbin : |eta-center| ≤ radius/W) :
    cEta ≤ w*eta ∧ w*eta ≤ CEta := by
  have h := abs_le.mp hbin
  have h₁ := mul_le_mul_of_nonneg_left h.1 hw.le
  have h₂ := mul_le_mul_of_nonneg_left h.2 hw.le
  have heq : w*(radius/W)=radius*(w/W) := by ring
  rw [mul_neg, heq] at h₁
  rw [heq] at h₂
  constructor <;> nlinarith only [h₁,h₂,hlo,hhi]

theorem physical_synthesis_annulus (chi : SchwartzMap (ℝ×ℝ) ℂ) (A B : ℝ)
    (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (nu : SymbolSpace) (q : ℕ) (l W theta center w cEta CEta : ℝ)
    (hl : 0<l) (hW : 0<W) (hw : 0<w)
    (hlo : cEta+(2*Real.pi*B)*(w/W) ≤ w*(2*Real.pi*center))
    (hhi : w*(2*Real.pi*center)+(2*Real.pi*B)*(w/W) ≤ CEta)
    (z : ℝ×ℝ) (xi eta : ℝ)
    (h : planarAngularFourier (physicalPlanarPacket
      (synthesisProfile (planarInverseSchwartz chi) q nu) z.1 z.2
        l W theta (2*Real.pi*center) hl.ne' hW.ne') (xi,eta)≠0) :
    |xi+theta*eta|≤(2*Real.pi*A)/l ∧ cEta≤w*eta ∧ w*eta≤CEta := by
  have hs := synthesisProfile_angular_support chi A B hchi nu q l W theta center hl hW z xi eta h
  exact ⟨hs.1,bin_support_annulus w W (2*Real.pi*center) (2*Real.pi*B)
    cEta CEta eta hw hW hlo hhi hs.2⟩

theorem physical_analysis_annulus (chi : SchwartzMap (ℝ×ℝ) ℂ) (A B : ℝ)
    (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (nu : SymbolSpace) (q : ℕ) (l W theta center w cEta CEta : ℝ)
    (hl : 0<l) (hW : 0<W) (hw : 0<w)
    (hlo : cEta+(2*Real.pi*B)*(w/W) ≤ w*(2*Real.pi*center))
    (hhi : w*(2*Real.pi*center)+(2*Real.pi*B)*(w/W) ≤ CEta)
    (z : ℝ×ℝ) (xi eta : ℝ)
    (h : planarAngularFourier (physicalPlanarPacket
      (analysisProfile (planarInverseSchwartz chi) q nu) z.1 z.2
        l W theta (2*Real.pi*center) hl.ne' hW.ne') (xi,eta)≠0) :
    |xi+theta*eta|≤(2*Real.pi*A)/l ∧ cEta≤w*eta ∧ w*eta≤CEta := by
  have hs := analysisProfile_angular_support chi A B hchi nu q l W theta center hl hW z xi eta h
  exact ⟨hs.1,bin_support_annulus w W (2*Real.pi*center) (2*Real.pi*B)
    cEta CEta eta hw hW hlo hhi hs.2⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
