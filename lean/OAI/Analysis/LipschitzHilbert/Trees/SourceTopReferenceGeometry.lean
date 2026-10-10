import OAI.Analysis.LipschitzHilbert.Packets.SourcePacketDensity

namespace OAI

/-! A selected top supplies the exact reference-cone and center bounds
for the ordinary tree estimate. -/
noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem selected_top_cone (w : ℝ) (hw : 0<w)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (q : P.PacketIndex) (T : SlopeBox)
    (hlen : P.length q.1≤T.length)
    (hrow : P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (htop : T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) :
    |P.rowSlope q.1 q.2.1-T.slope|≤w/P.length q.1 := by
  have h := P.referenceCondition_of_density_cell 0 cell grid w 1 hw (by norm_num)
    q T hlen (by simpa only [zero_add] using hrow) htop
  simpa only [zero_add,one_mul,abs_sub_comm] using h.2

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

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
