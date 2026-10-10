import OAI.Analysis.LipschitzHilbert.Geometry.SourceSelectedPacketPacking
import OAI.Analysis.LipschitzHilbert.Packets.SourceReferencePacketEnvelope

namespace OAI

/-! The short-envelope estimate for an actual positive size-selection
run, with the spatial and angular widths kept independent. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice.SizeStoppingRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : SourceLabeledLattice N κ Label Item}
  {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

def selectedEnvelopePackingConstant (cb : ℝ) (gap M Q : ℕ) : ℝ :=
  (gap:ℝ)*((((2*Q+1)*M:ℕ):ℝ)*(((1+(1:ℝ)^2)*(1+((1:ℝ)*(1+cb/4))^2))*(4*Real.pi)^2))

theorem selected_short_envelope_energy
    (h : P.SizeStoppingRun false w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hw : 0<w) (hwW : w≤P.width) (hcb : 0<cb)
    (t CZero a b L : ℝ) (hL : 0<L) (hCZero : 0<CZero)
    (hconstants : (1+cb/4)/CZero≤cb/4)
    (hA : 2*(1+(1+cb/4))+1/2≤A)
    (gap M Q : ℕ) (hgap : CZero≤(2:ℝ)^gap) (hQ : cb/4≤Q)
    (S : Finset P.PacketIndex)
    (hselected : ∀ q∈S, ∃ p∈P.sizeSelectionRecords false w cb A cell grid initial tops, q∈p.2)
    (hmultiplicity : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M)
    (hlen : ∀ q∈S, P.length q.1≤L)
    (hnear : ∀ q∈S, |P.rowSlope q.1 q.2.1-t|≤cb*(w/P.length q.1)/4)
    (hrow : ∀ q∈S, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (hepsilon : ∀ q∈S, epsilon≤cb*(w/P.length q.1)/4)
    (hmargin : ∀ q∈S, Icc (P.rowSlope q.1 q.2.1-cb*(w/P.length q.1)/2)
      (P.rowSlope q.1 q.2.1+cb*(w/P.length q.1)/2)⊆
        scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) :
    let F := fun z => shearedTopReciprocal a b L P.width t z*
      ∑ q∈S, shearedTileEnvelope (P.actualX q.1 q.2.1 q.2.2)
        (P.actualZ q.1 q.2.1 q.2.2) (P.length q.1) P.width t 2 z
    Integrable (fun z => (F z)^2) (volume.prod volume) ∧
      (∫ z, (F z)^2 ∂volume.prod volume)≤
        (82944*selectedEnvelopePackingConstant cb gap M Q)^2*1296*Real.pi^2*L*P.width := by
  have hpack := h.selected_packet_box_packing hw hwW hcb t 1 CZero (by norm_num) hCZero
    hconstants (by simpa only [mul_one,one_mul] using hA) gap M Q hgap hQ S hselected
    hmultiplicity hnear hrow hepsilon hmargin
  apply sheared_packed_envelope_energy S
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.actualZ q.1 q.2.1 q.2.2)
    (fun q => P.length q.1) a b L P.width t (selectedEnvelopePackingConstant cb gap M Q)
    hL P.width_pos (fun q _ => P.length_pos q.1) hlen
  intro z
  simpa only [densitySpatialBox,directionBox,mem_ofPred_eq,one_mul,selectedEnvelopePackingConstant] using hpack z

end LipschitzHilbert.SourceLabeledLattice.SizeStoppingRun

end

end OAI
