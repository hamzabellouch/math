import OAI.Analysis.LipschitzHilbert.Packets.PacketDataModelConfig

namespace OAI

/-! Restriction keeps the same geometric constants and selector. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData.OrdinaryModelConfig
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
  {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

def restrict (d : OrdinaryModelConfig P initial) (S : Finset P.PacketIndex) (hS : S⊆initial) :
    OrdinaryModelConfig P S where
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
  hrow := fun q hq => d.hrow q (hS hq)
  hlength := fun q hq => d.hlength q (hS hq)
  heps := fun q hq => d.heps q (hS hq)
  spectrum := d.spectrum
  margin_spectrum := fun q hq => d.margin_spectrum q (hS hq)
  bin := fun q hq => d.bin q (hS hq)
  measurable := d.measurable
  bounded := d.bounded
  away := d.away
  support := d.support
  radius_bound := d.radius_bound
  near := d.near

end LipschitzHilbert.PacketLatticeData.OrdinaryModelConfig

end

end OAI
