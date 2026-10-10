import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectedPackets
import OAI.Analysis.LipschitzHilbert.Phase.SourceSelectionAngularGeometry

namespace OAI

/-! Geometry of each actual recorded test, in its own top coordinates. -/
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

theorem recorded_packet_geometry
    (h : P.SizeStoppingRun false w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hw : 0<w)
    (hrow : ∀ q∈P.selectedPackets false w cb A cell grid initial tops,
      P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (p : SlopeBox × Finset P.PacketIndex)
    (hp : p∈P.sizeSelectionRecords false w cb A cell grid initial tops)
    (q : P.PacketIndex) (hq : q∈p.2) :
    P.length q.1≤p.1.length ∧
      |P.actualX q.1 q.2.1 q.2.2-p.1.x|≤p.1.length ∧
      |(P.actualZ q.1 q.2.1 q.2.2-p.1.y)-p.1.slope*(P.actualX q.1 q.2.1 q.2.2-p.1.x)|≤P.width ∧
      cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-p.1.slope| ∧
      |P.rowSlope q.1 q.2.1-p.1.slope|≤w/P.length q.1 := by
  have hg := (h.records_geometry p hp).2.2 q hq
  have hwidth := (h.records_geometry p hp).1
  have hs : q∈P.selectedPackets false w cb A cell grid initial tops :=
    (P.mem_selectedPackets false w cb A cell grid initial tops q).mpr ⟨p,hp,hq⟩
  have hbox := hg.2.1
  change |P.actualX q.1 q.2.1 q.2.2-p.1.x|≤(1/2)*p.1.length ∧
    |(P.actualZ q.1 q.2.1 q.2.2-p.1.y)-p.1.slope*(P.actualX q.1 q.2.1 q.2.2-p.1.x)|≤
      (1/2)*p.1.width at hbox
  rw [hwidth] at hbox
  have hlower := hg.2.2.2
  change cb*w/P.length q.1≤p.1.slope-P.rowSlope q.1 q.2.1 at hlower
  refine ⟨hg.1,?_,?_,?_,?_⟩
  · exact hbox.1.trans (by linarith [p.1.length_pos])
  · exact hbox.2.trans (by linarith [P.width_pos])
  · rw [abs_sub_comm]
    exact hlower.trans (le_abs_self _)
  · exact P.angular_cell_distance w hw grid q.1 (cell q.1 q.2.1) _ _ (hrow q hs) hg.2.2.1

end LipschitzHilbert.SourceLabeledLattice.SizeStoppingRun

namespace LipschitzHilbert

theorem short_direction_shear_bound (theta t cb w ell W : ℝ)
    (hell : 0<ell) (hW : 0<W) (hw : 0≤w) (hwW : w≤W) (hcb : cb≤4)
    (hnear : |theta-t|≤cb*(w/ell)/4) : |(theta-t)*ell/W|≤1 := by
  rw [abs_div,abs_mul,abs_of_pos hell,abs_of_pos hW]
  apply (div_le_one hW).mpr
  have hscaled := mul_le_mul_of_nonneg_right hnear hell.le
  have he : (cb*(w/ell)/4)*ell=cb*w/4 := by field_simp
  rw [he] at hscaled
  have hc := mul_le_mul_of_nonneg_right hcb hw
  have hb : cb*w/4≤W := by linarith
  exact hscaled.trans hb

end LipschitzHilbert

end

end OAI
