import OAI.Analysis.LipschitzHilbert.Packets.PacketDataModelCostPolynomial
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataCrossValue

namespace OAI

/-! Auxiliary derivative normalization leaves all physical packet values
and masked analyzing coefficients unchanged. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

abbrev withJetControl (P : PacketLatticeData N κ Label Item) (scale ratio : ℝ)
    (hratio : 1≤ratio) (hscale : |scale/P.width|≤ratio) : PacketLatticeData N κ Label Item :=
  { P with scale := scale, ratioBound := ratio, ratioBound_ge_one := hratio, scale_bound := hscale }

@[simp] theorem withJetControl_crossPacketValue (P : PacketLatticeData N κ Label Item)
    (scale ratio : ℝ) (hratio : 1≤ratio) (hscale : |scale/P.width|≤ratio)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (u : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) (q : P.PacketIndex) :
    (P.withJetControl scale ratio hratio hscale).crossPacketValue alt hAlt t b u g z q=
      P.crossPacketValue alt hAlt t b u g z q := rfl

namespace OrdinaryModelConfig
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
  {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

def withJetControl (d : OrdinaryModelConfig P initial) (scale ratio : ℝ)
    (hratio : 1≤ratio) (hscale : |scale/P.width|≤ratio) :
    OrdinaryModelConfig (P.withJetControl scale ratio hratio hscale) initial where
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
  spectrum := d.spectrum
  margin_spectrum := d.margin_spectrum
  bin := d.bin
  measurable := d.measurable
  bounded := d.bounded
  away := d.away
  support := d.support
  radius_bound := d.radius_bound
  near := d.near

end OrdinaryModelConfig
end LipschitzHilbert.PacketLatticeData

end

end OAI
