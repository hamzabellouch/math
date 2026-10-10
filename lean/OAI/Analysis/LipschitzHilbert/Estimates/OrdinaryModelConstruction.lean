import OAI.Analysis.LipschitzHilbert.Estimates.OrdinaryModelNumerics

namespace OAI

/-! Construct the ordinary model from its geometric data. The numerical
parameters are fixed before the finite packet collection is chosen. The
auxiliary positive cutoff is chosen below every packet's angular scale. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem length_le_topLength (P : PacketLatticeData N κ Label Item) (j : Fin N) :
    P.length j≤P.topLength := by
  apply (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ)<2) _)).mpr
  have h : (1:ℝ)≤2^j.val := one_le_pow₀ (by norm_num)
  nlinarith [P.topLength_pos]

def ordinaryModelOfGeometry (P : PacketLatticeData N κ Label Item)
    (initial : Finset P.PacketIndex)
    (cStar cEta CEta cb Cv w F radius : ℝ) (M : ℕ)
    (hcStar : 0≤cStar) (hcEta : 0<cEta) (hCEta : 0≤CEta) (hCv : 0≤Cv)
    (hcb : 0<cb) (hcbQuarter : cb≤1/4) (hsmall : cStar/cEta<cb/4)
    (num : OrdinaryModelNumerics cStar cEta cb radius)
    (hw : 0<w) (hW : w≤P.width) (hF : 0≤F) (hr : 0≤radius)
    (horder : 207≤P.order) (hfreq : ∀ k, |P.frequency k|≤F/w)
    (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (hrow : ∀ q∈initial, P.rowSlope q.1 q.2.1∈
      scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (spectrum : ∀ j l a k xi et,
      planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta)
    (margin_spectrum : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        Icc (-xi/et-cb*(w/P.length q.1)) (-xi/et+cb*(w/P.length q.1))⊆
          scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (bin : ∀ j l a k xi et,
      planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (measurable : ∀ j l k, Measurable (selector j l k))
    (bounded : ∀ j l k s, ‖selector j l k s‖≤1)
    (away : ∀ j l k s, selector j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|)
    (support : ∀ j l k s, selector j l k s≠0 →
      s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l))
    (radius_bound : ∀ j l k s, selector j l k s≠0 →
      |s-P.rowSlope j l|≤radius*(w/P.length j))
    (near : ∀ j l k s t, |s-t|≤w/P.length j →
      ‖selector j l k s-selector j l k t‖≤|s-t|/(w/P.length j)) :
    OrdinaryModelConfig P initial where
  cStar := cStar
  cEta := cEta
  CEta := CEta
  cb := cb
  Cv := Cv
  w := w
  tau := P.topLength
  epsilon := cb*w/(4*P.topLength)
  A := 5
  margin := cb
  F := F
  radius := radius
  Lip := 1
  M := M
  Q := 1
  gap := num.gap
  packGap := num.packGap
  R := 1
  K := num.K
  D0 := 5
  cell := cell
  grid := grid
  selector := selector
  hcStar := hcStar
  hcEta := hcEta
  hCEta := hCEta
  hCv := hCv
  hcb := hcb
  hcbQuarter := hcbQuarter
  hspectral := by
    have h : cStar/cEta<cb := by linarith
    simpa only [mul_comm] using (div_lt_iff₀ hcEta).mp h
  hepsilon := div_pos (mul_pos hcb hw) (mul_pos (by norm_num) P.topLength_pos)
  hw := hw
  hW := hW
  hF := hF
  hfreq := hfreq
  hgap := num.hgap
  hpack := num.hpack
  hmargin := by linarith
  hA := by linarith
  hQ := by norm_num; linarith
  hQnear := by
    norm_num only [Nat.cast_one]
    rw [show 2*cStar/cEta=2*(cStar/cEta) by ring]
    linarith
  hR := by norm_num
  horder := horder
  hD0 := by norm_num
  htime := le_rfl
  hwide := by linarith
  hK := num.hK
  hLip := by norm_num
  hlocal := hlocal
  hrow := hrow
  hlength := fun q _ => P.length_le_topLength q.1
  heps := by
    intro q _
    have hl := P.length_pos q.1
    have hle := P.length_le_topLength q.1
    calc
      cb*w/(4*P.topLength) = (cb*w/4)/P.topLength := by ring
      _ ≤ (cb*w/4)/P.length q.1 := div_le_div_of_nonneg_left (by positivity) hl hle
      _ = cb*(w/P.length q.1)/4 := by ring
  spectrum := spectrum
  margin_spectrum := margin_spectrum
  bin := fun s _ => bin s.1 s.2.1 s.2.2
  measurable := measurable
  bounded := bounded
  away := away
  support := support
  radius_bound := radius_bound
  near := by simpa only [one_mul] using near

end LipschitzHilbert.PacketLatticeData

end

end OAI
