import OAI.Analysis.LipschitzHilbert.Packets.PacketDataModelConfig
import OAI.Analysis.LipschitzHilbert.Packets.PacketLatticeRestriction
import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticePolarizationSpectrum

namespace OAI

/-! Four-phase profile combinations on the original labeled geometry,
including transport of the exact ordinary-model hypotheses. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)

abbrev polarize (c : ℂ) (hc : ‖c‖=1) : PacketLatticeData N κ Label Item :=
  { P with
    profileBound := 2*P.profileBound
    profileBound_pos := mul_pos (by norm_num) P.profileBound_pos
    profile := fun j l a k => P.profile j l a k+c • alt j l a k
    profile_bound := fun j l a k => planarProfileConstant_polarization_bound
      (P.profile j l a k) (alt j l a k) c hc (2*P.order) P.profileBound
      (P.profile_bound j l a k) (hAlt j l a k) }

theorem polarize_physicalPacket (c : ℂ) (hc : ‖c‖=1)
    (t : ℝ) (j : Fin N) (l : P.labels j) (a : Item j l) (k : κ) :
    (P.polarize alt hAlt c hc).physicalPacket t j l a k=
      P.physicalPacket t j l a k+c • (P.withProfile alt hAlt).physicalPacket t j l a k := by
  apply physicalPlanarPacket_add_smul

theorem polarize_fourier_nonzero (c : ℂ) (hc : ‖c‖=1)
    (t : ℝ) (j : Fin N) (l : P.labels j) (a : Item j l) (k : κ) (xi eta : ℝ)
    (hn : planarAngularFourier ((P.polarize alt hAlt c hc).physicalPacket t j l a k) (xi,eta)≠0) :
    planarAngularFourier (P.physicalPacket t j l a k) (xi,eta)≠0 ∨
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket t j l a k) (xi,eta)≠0 := by
  by_cases h : planarAngularFourier (P.physicalPacket t j l a k) (xi,eta)=0
  · right
    intro h'
    apply hn
    rw [P.polarize_physicalPacket alt hAlt c hc,planarAngularFourier_add_smul,h,h',mul_zero,add_zero]
  · exact Or.inl h

namespace OrdinaryModelConfig
variable {P} {initial : Finset P.PacketIndex}

def polarize (d : OrdinaryModelConfig P initial)
    (c : ℂ) (hc : ‖c‖=1)
    (hSpectrum : ∀ j l a k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤d.cStar/P.length j ∧ d.cEta≤d.w*et ∧ d.w*et≤d.CEta)
    (hMargin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        Set.Icc (-xi/et-d.margin*(d.w/P.length q.1)) (-xi/et+d.margin*(d.w/P.length q.1))⊆
          scaledAngularCell (d.w/P.topLength) d.grid q.1.val (d.cell q.1 q.2.1))
    (hBin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        |et-P.frequency k|≤d.Cv/P.width) :
    OrdinaryModelConfig (P.polarize alt hAlt c hc) initial where
  cStar := d.cStar
  cEta := d.cEta
  CEta := d.CEta
  cb := d.cb
  Cv := d.Cv
  w := d.w
  tau := d.tau
  epsilon := d.epsilon
  A := d.A
  margin := d.margin
  F := d.F
  radius := d.radius
  Lip := d.Lip
  M := d.M
  Q := d.Q
  gap := d.gap
  packGap := d.packGap
  R := d.R
  K := d.K
  D0 := d.D0
  cell := d.cell
  grid := d.grid
  selector := d.selector
  hcStar := d.hcStar
  hcEta := d.hcEta
  hCEta := d.hCEta
  hCv := d.hCv
  hcb := d.hcb
  hcbQuarter := d.hcbQuarter
  hspectral := d.hspectral
  hepsilon := d.hepsilon
  hw := d.hw
  hW := d.hW
  hF := d.hF
  hfreq := d.hfreq
  hgap := d.hgap
  hpack := d.hpack
  hmargin := d.hmargin
  hA := d.hA
  hQ := d.hQ
  hQnear := d.hQnear
  hR := d.hR
  horder := d.horder
  hD0 := d.hD0
  htime := d.htime
  hwide := d.hwide
  hK := d.hK
  hLip := d.hLip
  hlocal := d.hlocal
  hrow := d.hrow
  hlength := d.hlength
  heps := d.heps
  measurable := d.measurable
  bounded := d.bounded
  away := d.away
  support := d.support
  radius_bound := d.radius_bound
  near := d.near
  spectrum := fun j l a k xi et hn => by
    rcases P.polarize_fourier_nonzero alt hAlt c hc 0 j l a k xi et hn with h | h
    · exact d.spectrum j l a k xi et h
    · exact hSpectrum j l a k xi et h
  margin_spectrum := fun q hq k xi et hn => by
    rcases P.polarize_fourier_nonzero alt hAlt c hc 0 q.1 q.2.1 q.2.2 k xi et hn with h | h
    · exact d.margin_spectrum q hq k xi et h
    · exact hMargin q hq k xi et h
  bin := fun q hq k xi et hn => by
    rcases P.polarize_fourier_nonzero alt hAlt c hc 0 q.1 q.2.1 q.2.2 k xi et hn with h | h
    · exact d.bin q hq k xi et h
    · exact hBin q hq k xi et h

end OrdinaryModelConfig
end LipschitzHilbert.PacketLatticeData

end

end OAI
