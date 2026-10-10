import OAI.Analysis.LipschitzHilbert.Phase.PacketDataSignedAngularGeometry
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedPackets
import OAI.Analysis.LipschitzHilbert.Phase.PacketDataSelectionAngularGeometry

namespace OAI

/-! Geometry of each actual recorded test, in its own top coordinates. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketLatticeData.SizeStoppingRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : PacketLatticeData N κ Label Item} {negative : Bool}
  {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem recorded_packet_geometry_signed
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hw : 0<w)
    (hrow : ∀ q∈P.selectedPackets negative w cb A cell grid initial tops,
      P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (p : SlopeBox × Finset P.PacketIndex)
    (hp : p∈P.sizeSelectionRecords negative w cb A cell grid initial tops)
    (q : P.PacketIndex) (hq : q∈p.2) :
    P.length q.1≤p.1.length ∧
      |P.actualX q.1 q.2.1 q.2.2-p.1.x|≤p.1.length ∧
      |(P.actualZ q.1 q.2.1 q.2.2-p.1.y)-p.1.slope*(P.actualX q.1 q.2.1 q.2.2-p.1.x)|≤P.width ∧
      cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-p.1.slope| ∧
      |P.rowSlope q.1 q.2.1-p.1.slope|≤w/P.length q.1 := by
  have hg := (h.records_geometry p hp).2.2 q hq
  have hwidth := (h.records_geometry p hp).1
  have hs : q∈P.selectedPackets negative w cb A cell grid initial tops :=
    (P.mem_selectedPackets negative w cb A cell grid initial tops q).mpr ⟨p,hp,hq⟩
  have hbox := hg.2.1
  change |P.actualX q.1 q.2.1 q.2.2-p.1.x|≤(1/2)*p.1.length ∧
    |(P.actualZ q.1 q.2.1 q.2.2-p.1.y)-p.1.slope*(P.actualX q.1 q.2.1 q.2.2-p.1.x)|≤
      (1/2)*p.1.width at hbox
  rw [hwidth] at hbox
  have hlower := hg.2.2.2
  have habs : sizeDirection negative (p.1.slope-P.rowSlope q.1 q.2.1)≤
      |p.1.slope-P.rowSlope q.1 q.2.1| := by
    cases negative
    · exact le_abs_self _
    · exact neg_le_abs _
  refine ⟨hg.1,?_,?_,?_,?_⟩
  · exact hbox.1.trans (by linarith [p.1.length_pos])
  · exact hbox.2.trans (by linarith [P.width_pos])
  · rw [abs_sub_comm]
    exact hlower.trans habs
  · exact P.angular_cell_distance w hw grid q.1 (cell q.1 q.2.1) _ _ (hrow q hs) hg.2.2.1

end LipschitzHilbert.PacketLatticeData.SizeStoppingRun

end

end OAI
