import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensity

namespace OAI

/-! A selected top supplies the exact reference-cone and center bounds
for the ordinary tree estimate. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem selected_top_cone (w : ℝ) (hw : 0<w)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (q : P.PacketIndex) (T : SlopeBox)
    (_hlen : P.length q.1≤T.length)
    (hrow : P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (htop : T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) :
    |P.rowSlope q.1 q.2.1-T.slope|≤w/P.length q.1 := by
  have hs := scaledAngularCell_slope (div_pos hw P.topLength_pos)
    (le_refl (q.1.val:ℤ)) ⟨P.rowSlope q.1 q.2.1,hrow,hrow⟩ hrow htop
  have heq : (w/P.topLength)*DyadicLineGrid.scale (q.1.val:ℤ) = w/P.length q.1 := by
    simp only [DyadicLineGrid.scale,zpow_natCast,PacketLatticeData.length]
    field_simp [P.topLength_pos.ne',ne_of_gt (pow_pos (by norm_num : (0:ℝ)<2) q.1.val)]
  rw [heq] at hs
  exact hs

theorem selected_top_centers (T : SlopeBox) (A : ℝ) (q : P.PacketIndex)
    (hwidth : T.width=P.width)
    (hcenter : (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T A) :
    |P.actualX q.1 q.2.1 q.2.2-T.x|≤A*T.length ∧
    |P.actualZ q.1 q.2.1 q.2.2-T.slope*P.actualX q.1 q.2.1 q.2.2-
      (T.y-T.slope*T.x)|≤A*P.width := by
  change |P.actualX q.1 q.2.1 q.2.2-T.x|≤A*T.length ∧
    |(P.actualZ q.1 q.2.1 q.2.2-T.y)-T.slope*(P.actualX q.1 q.2.1 q.2.2-T.x)|≤A*T.width at hcenter
  refine ⟨hcenter.1,?_⟩
  rw [hwidth] at hcenter
  convert hcenter.2 using 1
  congr 1
  ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
