import OAI.Analysis.LipschitzHilbert.Packets.NormalizedPacketLattice
import OAI.Analysis.LipschitzHilbert.Packets.PacketBinAnnulus
import OAI.Analysis.LipschitzHilbert.Packets.PacketLatticeRestriction

namespace OAI

/-! The literal normalized finite lattices inherit the frequency strip,
positive annulus, and carrier bin from their fixed Fourier plateaus. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (chi : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
  (topLength width scale ratioBound C : ℝ) (order : ℕ)
  (htop : 0<topLength) (hwidth : 0<width) (hC : 0<C) (horder : 3≤order)
  (hratio : 1≤ratioBound) (hscale : |scale/width|≤ratioBound)
  (labels : ∀ j, Finset (Label j))
  (originX originZ theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
  (site : ∀ j (l : labels j), Item j l → ℤ×ℤ)
  (hinj : ∀ j l, Function.Injective (site j l))
  (hprofile : planarProfileConstant (synthesisProfile (planarInverseSchwartz chi) q nu) (2*order) ≤ C)

local notation "P" => normalizedPacketLattice (planarInverseSchwartz chi) q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile


variable (A B : ℝ) (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
  (w cEta CEta : ℝ) (hw : 0<w)
  (hlo : ∀ k, cEta+(2*Real.pi*B)*(w/width)≤w*(2*Real.pi*center k))
  (hhi : ∀ k, w*(2*Real.pi*center k)+(2*Real.pi*B)*(w/width)≤CEta)

include hchi hw hlo hhi in
theorem normalizedPacketLattice_spectrum (j : Fin N) (l : (P).labels j)
    (a : Item j l) (k : κ) (xi eta : ℝ)
    (hs : planarAngularFourier ((P).physicalPacket 0 j l a k) (xi,eta)≠0) :
    (|xi+(P).rowSlope j l*eta|≤(2*Real.pi*A)/(P).length j ∧
      cEta≤w*eta ∧ w*eta≤CEta) ∧
    |eta-(P).frequency k|≤(2*Real.pi*B)/(P).width := by
  have hs' : planarAngularFourier (physicalPlanarPacket
      (synthesisProfile (planarInverseSchwartz chi) q nu)
      ((P).actualX j l a) ((P).actualZ j l a) ((P).length j) width (theta j l)
      (2*Real.pi*center k) ((P).length_pos j).ne' hwidth.ne') (xi,eta)≠0 := by
    change planarAngularFourier (physicalPlanarPacket
      (synthesisProfile (planarInverseSchwartz chi) q nu)
      ((P).actualX j l a) ((P).actualZ j l a+0*(P).actualX j l a)
      ((P).length j) width (0+theta j l) (2*Real.pi*center k) _ _) (xi,eta)≠0 at hs
    simpa only [zero_mul,add_zero,zero_add] using hs
  exact ⟨physical_synthesis_annulus chi A B hchi nu q ((P).length j) width
    (theta j l) (center k) w cEta CEta ((P).length_pos j) hwidth hw (hlo k) (hhi k)
    ((P).actualX j l a,(P).actualZ j l a) xi eta hs',
    (synthesisProfile_angular_support chi A B hchi nu q ((P).length j) width
      (theta j l) (center k) ((P).length_pos j) hwidth
      ((P).actualX j l a,(P).actualZ j l a) xi eta hs').2⟩

variable (chiB : SchwartzMap (ℝ×ℝ) ℂ)
  (hBprofile : planarProfileConstant (analysisProfile (planarInverseSchwartz chiB) q nu) (2*order)≤C)
local notation "alt" => normalizedAnalysisFamily (planarInverseSchwartz chi) q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile (planarInverseSchwartz chiB)
local notation "hAlt" => normalizedAnalysisFamily_bound (planarInverseSchwartz chi) q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile (planarInverseSchwartz chiB) hBprofile

include hw hlo hhi in
theorem normalizedAnalysisFamily_spectrum
    (hchiB : ∀ z, chiB z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (j : Fin N) (l : (P).labels j) (a : Item j l) (k : κ) (xi eta : ℝ)
    (hs : planarAngularFourier (((P).withProfile alt hAlt).physicalPacket 0 j l a k)
      (xi,eta)≠0) :
    (|xi+(P).rowSlope j l*eta|≤(2*Real.pi*A)/(P).length j ∧
      cEta≤w*eta ∧ w*eta≤CEta) ∧
    |eta-(P).frequency k|≤(2*Real.pi*B)/(P).width := by
  have hs' : planarAngularFourier (physicalPlanarPacket
      (analysisProfile (planarInverseSchwartz chiB) q nu)
      ((P).actualX j l a) ((P).actualZ j l a) ((P).length j) width (theta j l)
      (2*Real.pi*center k) ((P).length_pos j).ne' hwidth.ne') (xi,eta)≠0 := by
    change planarAngularFourier (physicalPlanarPacket
      (analysisProfile (planarInverseSchwartz chiB) q nu)
      ((P).actualX j l a) ((P).actualZ j l a+0*(P).actualX j l a)
      ((P).length j) width (0+theta j l) (2*Real.pi*center k) _ _) (xi,eta)≠0 at hs
    simpa only [zero_mul,add_zero,zero_add] using hs
  exact ⟨physical_analysis_annulus chiB A B hchiB nu q ((P).length j) width
    (theta j l) (center k) w cEta CEta ((P).length_pos j) hwidth hw (hlo k) (hhi k)
    ((P).actualX j l a,(P).actualZ j l a) xi eta hs',
    (analysisProfile_angular_support chiB A B hchiB nu q ((P).length j) width
      (theta j l) (center k) ((P).length_pos j) hwidth
      ((P).actualX j l a,(P).actualZ j l a) xi eta hs').2⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
