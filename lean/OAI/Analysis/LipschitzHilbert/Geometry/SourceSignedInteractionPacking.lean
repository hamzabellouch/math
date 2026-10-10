import OAI.Analysis.LipschitzHilbert.Geometry.SourceSignedPacketPacking
import OAI.Analysis.LipschitzHilbert.Trees.SourceInteractionGeometry
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectedPackets

namespace OAI

/-! Actual Gram-interacting short packets from one selected top obey
the packing estimate needed by the far-tree bound. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.SourceLabeledLattice.SizeStoppingRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : SourceLabeledLattice N κ Label Item} {negative : Bool}
  {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem selected_interacting_box_packing_signed
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hw : 0<w) (hwW : w≤P.width) (hcb : 0<cb)
    (cStar cEta CEta margin : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (farGap packGap M Q : ℕ)
    (hfar : (cStar/cEta)*(1+1/(2:ℝ)^farGap)+1/(2:ℝ)^farGap≤cb/4)
    (hpack : (1+cb/4)/(2:ℝ)^packGap≤cb/4)
    (hmarginSize : cb/2≤margin-cStar/cEta)
    (hA : 2*(1+(1+cb/4))+1/2≤A) (hQ : cb/4≤Q)
    (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M)
    (hrow : ∀ q∈P.selectedPackets negative w cb A cell grid initial tops,
      P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (hepsilon : ∀ q∈P.selectedPackets negative w cb A cell grid initial tops,
      epsilon≤cb*(w/P.length q.1)/4)
    (hspectrum : ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
      |xi+P.rowSlope j l*eta|≤cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta)
    (hmargin : ∀ s∈P.selectedPackets negative w cb A cell grid initial tops, ∀ k xi eta,
      planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,eta)≠0 →
      Icc (-xi/eta-margin*(w/P.length s.1)) (-xi/eta+margin*(w/P.length s.1))⊆
        scaledAngularCell (w/P.topLength) grid s.1.val (cell s.1 s.2.1))
    (p : SlopeBox × Finset P.PacketIndex)
    (hp : p∈P.sizeSelectionRecords negative w cb A cell grid initial tops) :
    let S := P.interactingShortPackets (P.selectedPackets negative w cb A cell grid initial tops) p.2 farGap
    ∀ z : ℝ×ℝ, ((S.filter fun q => |z.1-P.actualX q.1 q.2.1 q.2.2|≤P.length q.1 ∧
      |(z.2-P.actualZ q.1 q.2.1 q.2.2)-p.1.slope*(z.1-P.actualX q.1 q.2.1 q.2.2)|≤P.width).card:ℝ)≤
        selectedEnvelopePackingConstant cb packGap M Q := by
  let all := P.selectedPackets negative w cb A cell grid initial tops
  let S := P.interactingShortPackets all p.2 farGap
  have hsub : S⊆all := P.interactingShortPackets_subset all p.2 farGap
  have hT (q : P.PacketIndex) (hq : q∈p.2) : |P.rowSlope q.1 q.2.1-p.1.slope|≤w/P.length q.1 := by
    have hs : q∈all := (P.mem_selectedPackets negative w cb A cell grid initial tops q).mpr ⟨p,hp,hq⟩
    exact P.angular_cell_distance w hw grid q.1 (cell q.1 q.2.1) _ _ (hrow q hs)
      ((h.records_geometry p hp).2.2 q hq).2.2.1
  have hnear := P.interacting_short_direction all p.2 farGap p.1.slope w cStar cEta CEta cb
    hw hcStar hcEta hfar hT hspectrum
  have hmargin' := P.interacting_short_margin all p.2 farGap w cStar cEta margin cb hw hcEta hmarginSize
    (fun q => scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (fun j l u k xi eta hh => ⟨(hspectrum j l u k xi eta hh).1,(hspectrum j l u k xi eta hh).2.1⟩)
    hmargin
  have hpacking := h.selected_packet_box_packing_signed hw hwW hcb p.1.slope 1 ((2:ℝ)^packGap)
    (by norm_num) (by positivity) hpack (by simpa only [one_mul,mul_one] using hA)
    packGap M Q le_rfl hQ S
    (fun q hq => (P.mem_selectedPackets negative w cb A cell grid initial tops q).mp (hsub hq))
    hlocal hnear (fun q hq => hrow q (hsub hq)) (fun q hq => hepsilon q (hsub hq)) hmargin'
  dsimp only
  intro z
  simpa only [densitySpatialBox,directionBox,mem_ofPred_eq,one_mul,selectedEnvelopePackingConstant] using hpacking z

end LipschitzHilbert.SourceLabeledLattice.SizeStoppingRun

end

end OAI
