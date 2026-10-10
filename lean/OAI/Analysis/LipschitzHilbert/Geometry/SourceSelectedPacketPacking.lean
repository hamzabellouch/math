import OAI.Analysis.LipschitzHilbert.Estimates.StoppingScaleIntervals
import OAI.Analysis.LipschitzHilbert.Geometry.SourceScalePacking
import OAI.Analysis.LipschitzHilbert.Packets.SourcePacketScaleCount

namespace OAI

/-! Bounded overlap for actual selected packets with slopes close to a
fixed longer tree. Both temporal order and spatial lattice counts have
been proved; no overlap premise is assumed. -/
noncomputable section
open Set
namespace LipschitzHilbert.SourceLabeledLattice.SizeStoppingRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : SourceLabeledLattice N κ Label Item}
  {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem selected_packet_box_packing
    (h : P.SizeStoppingRun false w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hw : 0<w) (hwW : w≤P.width) (hcb : 0<cb)
    (t K CZero : ℝ) (hK : 0≤K) (hCZero : 0<CZero)
    (hconstants : (1+cb/4)/CZero≤cb/4)
    (hA : 2*K*(1+(1+cb/4))+1/2≤A)
    (gap M Q : ℕ) (hgap : CZero≤(2:ℝ)^gap) (hQ : cb/4≤Q)
    (S : Finset P.PacketIndex)
    (hselected : ∀ q∈S, ∃ p∈P.sizeSelectionRecords false w cb A cell grid initial tops, q∈p.2)
    (hmultiplicity : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M)
    (hnear : ∀ q∈S, |P.rowSlope q.1 q.2.1-t|≤cb*(w/P.length q.1)/4)
    (hrow : ∀ q∈S, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (hepsilon : ∀ q∈S, epsilon≤cb*(w/P.length q.1)/4)
    (hmargin : ∀ q∈S, Icc (P.rowSlope q.1 q.2.1-cb*(w/P.length q.1)/2)
      (P.rowSlope q.1 q.2.1+cb*(w/P.length q.1)/2)⊆
        scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (z : ℝ×ℝ) :
    ((S.filter fun q => z∈densitySpatialBox (P.directionBox t q) K).card:ℝ)≤
      gap*((((2*Q+1)*M:ℕ):ℝ)*(((1+K^2)*(1+(K*(1+cb/4))^2))*(4*Real.pi)^2)) := by
  apply scale_window_packing S (fun q => q.1.val)
    (fun q => densitySpatialBox (P.directionBox t q) K) gap _ ?_ ?_ z
  · intro i hi j hj hij
    obtain ⟨p,hp,hpi⟩ := hselected i hi
    obtain ⟨p',hp',hpj⟩ := hselected j hj
    have hlen : P.length j.1≤P.length i.1 := P.length_antitone (by omega)
    have hfar : CZero*P.length j.1≤P.length i.1 :=
      (mul_le_mul_of_nonneg_right hgap (P.length_pos j.1).le).trans (P.length_scale_gap i.1 j.1 gap hij)
    exact (h.selected_boxes_disjoint_of_margin hw hwW hcb t K CZero hK hCZero hconstants hA
      p' p hp' hp j i hpj hpi hlen hfar (hnear j hj) (hnear i hi) (hrow i hi)
      (hepsilon j hj) (hmargin j hj)).symm
  · intro v k
    apply P.direction_packets_count S t w K (cb/4) hw hwW hK (by linarith) M Q hQ hmultiplicity
    intro q hq
    convert hnear q hq using 1; ring

end LipschitzHilbert.SourceLabeledLattice.SizeStoppingRun

end

end OAI
