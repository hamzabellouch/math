import OAI.Analysis.LipschitzHilbert.Trees.SourceHighDensityForest
import OAI.Analysis.LipschitzHilbert.Packets.SourceDensityPacketGeometry
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceMainRestriction

namespace OAI

/-! Ordinary density attached to literal source packets. A keeper in the
packet's original angular cell automatically meets the reference-cone
condition used by the phase-averaging argument. -/
noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

def densityTile (P : SourceLabeledLattice N κ Label Item) (oldSlope : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (q : P.PacketIndex) : OrdinaryDensityTile where
  center := (P.actualX q.1 q.2.1 q.2.2,
    P.actualZ q.1 q.2.1 q.2.2+oldSlope*P.actualX q.1 q.2.1 q.2.2)
  level := q.1.val
  cell := cell q.1 q.2.1

def ordinaryDensity (P : SourceLabeledLattice N κ Label Item) (oldSlope : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (w tau : ℝ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (q : P.PacketIndex) : ℝ :=
  (P.densityTile oldSlope cell q).density P.topLength w P.width tau grid E u

theorem densityTile_length (P : SourceLabeledLattice N κ Label Item) (oldSlope : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (q : P.PacketIndex) :
    P.topLength/DyadicLineGrid.scale (P.densityTile oldSlope cell q).level = P.length q.1 := by
  simp only [densityTile,DyadicLineGrid.scale,zpow_natCast,SourceLabeledLattice.length]

theorem referenceCondition_of_density_cell (P : SourceLabeledLattice N κ Label Item)
    (oldSlope : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (w cone : ℝ)
    (hw : 0 < w) (hcone : 1 ≤ cone) (q : P.PacketIndex) (T : SlopeBox)
    (hshort : P.length q.1 ≤ T.length)
    (horiginal : oldSlope+P.rowSlope q.1 q.2.1 ∈
      scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (htop : T.slope ∈ scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) :
    P.referenceCondition oldSlope T.slope T.length cone w q.1 q.2.1 := by
  refine ⟨hshort,?_⟩
  have hs := scaledAngularCell_slope (div_pos hw P.topLength_pos) (le_refl (q.1.val:ℤ))
    ⟨oldSlope+P.rowSlope q.1 q.2.1,horiginal,horiginal⟩ horiginal htop
  have heq : (w/P.topLength)*DyadicLineGrid.scale (q.1.val:ℤ) = w/P.length q.1 := by
    simp only [DyadicLineGrid.scale,zpow_natCast,SourceLabeledLattice.length]
    field_simp [P.topLength_pos.ne',ne_of_gt (pow_pos (by norm_num : (0:ℝ)<2) q.1.val)]
  rw [heq] at hs
  exact hs.trans (div_le_div_of_nonneg_right
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hcone hw.le) (P.length_pos q.1).le)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
