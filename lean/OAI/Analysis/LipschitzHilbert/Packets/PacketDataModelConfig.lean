import OAI.Analysis.LipschitzHilbert.Packets.PacketDataOrdinaryRemovalStep
import OAI.Analysis.LipschitzHilbert.Trees.SourceModelThresholdScale

namespace OAI

/-! Fixed geometric and selector data for the ordinary model. None of
these parameters depends on the input function or the tested set. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

structure OrdinaryModelConfig (P : PacketLatticeData N κ Label Item)
    (initial : Finset P.PacketIndex) where
  cStar : ℝ
  cEta : ℝ
  CEta : ℝ
  cb : ℝ
  Cv : ℝ
  w : ℝ
  tau : ℝ
  epsilon : ℝ
  A : ℝ
  margin : ℝ
  F : ℝ
  radius : ℝ
  Lip : ℝ
  M : ℕ
  Q : ℕ
  gap : ℕ
  packGap : ℕ
  R : ℕ
  K : ℕ
  D0 : ℕ
  cell : ∀ j, P.labels j → ℤ
  grid : ℤ
  selector : ∀ j, P.labels j → κ → ℝ → ℂ
  hcStar : 0≤cStar
  hcEta : 0<cEta
  hCEta : 0≤CEta
  hCv : 0≤Cv
  hcb : 0<cb
  hcbQuarter : cb≤1/4
  hspectral : cStar<cEta*cb
  hepsilon : 0<epsilon
  hw : 0<w
  hW : w≤P.width
  hF : 0≤F
  hfreq : ∀ k, |P.frequency k|≤F/w
  hgap : (cStar/cEta)*(1+1/(2:ℝ)^(gap+1))+1/(2:ℝ)^(gap+1)≤cb/4
  hpack : (1+cb/4)/(2:ℝ)^packGap≤cb/4
  hmargin : cb/2≤margin-cStar/cEta
  hA : 2*(1+(1+cb/4))+1/2≤A
  hQ : cb/4≤Q
  hQnear : 2*cStar/cEta≤Q
  hR : (1:ℝ)≤R
  horder : 207≤P.order
  hD0 : A≤D0
  htime : tau≤P.topLength
  hwide : 1≤radius+1
  hK : radius+1≤(2:ℝ)^K
  hLip : 0≤Lip
  hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M
  hrow : ∀ q∈initial, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
    grid q.1.val (cell q.1 q.2.1)
  hlength : ∀ q∈initial, P.length q.1≤tau
  heps : ∀ q∈initial, epsilon≤cb*(w/P.length q.1)/4
  spectrum : ∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
    |xi+P.rowSlope j l*et|≤cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta
  margin_spectrum : ∀ s∈initial, ∀ k xi et,
    planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,et)≠0 →
    Icc (-xi/et-margin*(w/P.length s.1)) (-xi/et+margin*(w/P.length s.1))⊆
      scaledAngularCell (w/P.topLength) grid s.1.val (cell s.1 s.2.1)
  bin : ∀ q∈initial, ∀ k xi et,
    planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
      |et-P.frequency k|≤Cv/P.width
  measurable : ∀ j l k, Measurable (selector j l k)
  bounded : ∀ j l k s, ‖selector j l k s‖≤1
  away : ∀ j l k s, selector j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|
  support : ∀ j l k s, selector j l k s≠0 →
    s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)
  radius_bound : ∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l|≤radius*(w/P.length j)
  near : ∀ j l k s t, |s-t|≤w/P.length j →
    ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j))

theorem referenceTreeConstant_nonneg (P : PacketLatticeData N κ Label Item)
    (C : ℝ) (B K : ℕ) (Lip : ℝ) (hLip : 0≤Lip) : 0≤P.referenceTreeConstant C B K Lip := by
  have ht := transverseTailConstant_nonneg
  have hp := P.profileBound_pos
  dsimp [referenceTreeConstant,referenceEnvelopeConstant]
  positivity

namespace OrdinaryModelConfig
variable {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

def sizeAreaConstant (d : OrdinaryModelConfig P initial) (CS : ℝ) : ℝ :=
  4*(selectedNearConstant P d.gap d.M d.Q+
    2*Real.sqrt (2*selectedFarConstant P d.cb (Real.sqrt 2) CS d.packGap d.M d.Q))

def stepConstant (d : OrdinaryModelConfig P initial) (CD CS CT : ℝ) : ℝ :=
  Real.sqrt 2*(2*(625*densityRadiusConstant^2*P.referenceTreeConstant CD ((2*d.R+1)*d.M) d.K d.Lip)+
    ((((4*d.D0+1)^2:ℕ):ℝ)*P.referenceTreeConstant CT ((2*d.R+1)*d.M) d.K d.Lip)*d.sizeAreaConstant CS)

theorem sizeAreaConstant_nonneg (d : OrdinaryModelConfig P initial) (CS : ℝ) :
    0≤d.sizeAreaConstant CS := by
  dsimp [sizeAreaConstant,selectedNearConstant]
  positivity

theorem stepConstant_nonneg (d : OrdinaryModelConfig P initial) (CD CS CT : ℝ) :
    0≤d.stepConstant CD CS CT := by
  have hd := P.referenceTreeConstant_nonneg CD ((2*d.R+1)*d.M) d.K d.Lip d.hLip
  have ht := P.referenceTreeConstant_nonneg CT ((2*d.R+1)*d.M) d.K d.Lip d.hLip
  have hs := d.sizeAreaConstant_nonneg CS
  dsimp only [stepConstant]
  positivity

end OrdinaryModelConfig
end LipschitzHilbert.PacketLatticeData

end

end OAI
