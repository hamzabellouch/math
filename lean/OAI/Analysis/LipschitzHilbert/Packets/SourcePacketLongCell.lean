import OAI.Analysis.LipschitzHilbert.Trees.SourceLongTreeSupport
import OAI.Analysis.LipschitzHilbert.Packets.SourcePacketDensity

namespace OAI

/-! Long-tree cell density for literal source packets. The test and its
common angular cell are obtained from the actual Whitney parent witness. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- The original long selectors all live in one angular cell whose mass
on every transverse strip has the density bound from the manuscript. -/
theorem source_whitney_cell_density (P : SourceLabeledLattice N κ Label Item)
    (oldSlope y : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid k j : ℤ) (w tau : ℝ)
    (htime : P.topLength≤tau)
    (hWhitney : Whitney (Finset.univ : Finset P.PacketIndex)
      (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1) k j)
    (hY : ∀ q : P.PacketIndex, |P.actualZ q.1 q.2.1 q.2.2-y|≤P.width/2)
    (hreference : ∀ q : P.PacketIndex, oldSlope∈
      scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (hlong : ∃ q : P.PacketIndex, 32*DyadicLineGrid.scale k<P.length q.1)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (eta : ℝ) (heta : 0≤eta)
    (hdensity : ∀ q, P.ordinaryDensity oldSlope cell grid w tau E u q≤eta) :
    ∃ q : P.PacketIndex, ∃ test : OrdinaryDensityTest P.topLength w P.width tau grid (P.densityTile oldSlope cell q),
      test.top.x=center k j ∧ test.top.y=y+oldSlope*center k j ∧ test.top.slope=oldSlope ∧
      16*DyadicLineGrid.scale k≤test.top.length ∧ test.top.length<32*DyadicLineGrid.scale k ∧
      (∀ r : P.PacketIndex, 32*DyadicLineGrid.scale k<P.length r.1 →
        scaledAngularCell (w/P.topLength) grid r.1.val (cell r.1 r.2.1) ⊆
          scaledAngularCell (w/P.topLength) grid test.level test.cell) ∧
      (∀ n : ℤ,
        let A := E∩u ⁻¹' scaledAngularCell (w/P.topLength) grid test.level test.cell∩
          treeCell oldSlope y P.width k j n
        IntegrableOn (fun _ : ℝ×ℝ => (1:ℝ)) A (volume.prod volume) ∧
        (volume.prod volume).real A≤32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*DyadicLineGrid.scale k*P.width) := by
  have hgeom : Whitney (Finset.univ : Finset P.PacketIndex)
      (fun q => (P.densityTile oldSlope cell q).center.1)
      (fun q => P.topLength/DyadicLineGrid.scale (P.densityTile oldSlope cell q).level) k j := by
    simpa only [densityTile,DyadicLineGrid.scale,zpow_natCast,SourceLabeledLattice.length] using hWhitney
  have hshort (q : P.PacketIndex) (_hq : q∈(Finset.univ : Finset P.PacketIndex)) :
      P.topLength/DyadicLineGrid.scale (P.densityTile oldSlope cell q).level≤tau := by
    rw [P.densityTile_length]
    exact (div_le_self P.topLength_pos.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))).trans htime
  have hcenter (q : P.PacketIndex) (_hq : q∈(Finset.univ : Finset P.PacketIndex)) :
      |(P.densityTile oldSlope cell q).center.2-y-oldSlope*(P.densityTile oldSlope cell q).center.1|≤P.width/2 := by
    have h := hY q
    convert h using 1
    congr 1
    dsimp [densityTile]
    ring
  have hangle (q : P.PacketIndex) (_hq : q∈(Finset.univ : Finset P.PacketIndex)) :
      oldSlope∈scaledAngularCell (w/P.topLength) grid
        (P.densityTile oldSlope cell q).level (P.densityTile oldSlope cell q).cell := hreference q
  have hlong' : ∃ q∈(Finset.univ : Finset P.PacketIndex), 32*DyadicLineGrid.scale k<
      P.topLength/DyadicLineGrid.scale (P.densityTile oldSlope cell q).level := by
    obtain ⟨q,hq⟩ := hlong
    exact ⟨q,Finset.mem_univ q,by simpa only [P.densityTile_length] using hq⟩
  obtain ⟨q,_hq,test,hx,hy,ht,hlo,hhi,hmass⟩ := exists_whitney_cell_density
    (Finset.univ : Finset P.PacketIndex) (P.densityTile oldSlope cell)
    P.topLength w P.width tau oldSlope y grid k j P.topLength_pos P.width_pos
    hgeom hshort hcenter hangle hlong' E hE u hu eta heta (fun q _ => hdensity q)
  refine ⟨q,test,hx,hy,ht,hlo,hhi,?_,hmass⟩
  intro r hr
  have hlen : test.top.length≤P.topLength/DyadicLineGrid.scale (P.densityTile oldSlope cell r).level := by
    rw [P.densityTile_length]
    exact hhi.le.trans hr.le
  exact test.contains_longer_angular_cell P.topLength_pos (P.densityTile oldSlope cell r)
    hlen (by simpa only [ht,densityTile] using hreference r)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
