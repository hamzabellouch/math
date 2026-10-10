import OAI.Analysis.LipschitzHilbert.Trees.SourceShearedEnvelopeEnergy
import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticeScaleEnergy
import OAI.Analysis.LipschitzHilbert.Estimates.ShearedEnvelope

namespace OAI

/-! Actual Schwartz packets are dominated by the envelope used in the
selected-tree cross-term estimate, in its common reference direction. -/
noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physicalPacket_reference_envelope (t : ℝ) (q : P.PacketIndex) (k : κ)
    (hclose : |(P.rowSlope q.1 q.2.1-t)*P.length q.1/P.width|≤1)
    (z : ℝ×ℝ) :
    ‖P.physicalPacket 0 q.1 q.2.1 q.2.2 k z‖≤
      (4*P.profileBound)*shearedTileEnvelope
        (P.actualX q.1 q.2.1 q.2.2) (P.actualZ q.1 q.2.1 q.2.2) (P.length q.1) P.width t 2 z := by
  let x := P.actualX q.1 q.2.1 q.2.2
  let y := P.actualZ q.1 q.2.1 q.2.2
  let theta := P.rowSlope q.1 q.2.1
  have h0 := physicalPlanarPacket_profile_envelope (P.profile q.1 q.2.1 q.2.2 k)
    (2*P.order) x y (P.length q.1) P.width theta (P.frequency k)
    (P.length_pos q.1).ne' P.width_pos.ne' z
  have ho : 4≤2*P.order := by have := P.order_ge_three; omega
  have hbound : ‖P.physicalPacket 0 q.1 q.2.1 q.2.2 k z‖≤P.profileBound*
      (lineEnvelope x (P.length q.1) 4 z.1*
        lineEnvelope (y-theta*x) P.width 4 (z.2-theta*z.1)) := by
    apply (show ‖P.physicalPacket 0 q.1 q.2.1 q.2.2 k z‖≤_ from by
      simpa only [physicalPacket,zero_mul,add_zero,zero_add] using h0).trans
    exact mul_le_mul (P.profile_bound q.1 q.2.1 q.2.2 k)
      (mul_le_mul (lineEnvelope_antitone _ _ _ ho) (lineEnvelope_antitone _ _ _ ho)
        (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
      (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
      P.profileBound_pos.le
  have hs := reference_shear_envelope z.1 z.2 x y (P.length q.1) P.width theta t 2
    (P.length_pos q.1) P.width_pos hclose
  have he (s : ℝ) : lineEnvelope (y-s*x) P.width 4 (z.2-s*z.1)=
      lineEnvelope (y+s*(z.1-x)) P.width 4 z.2 := by
    unfold lineEnvelope
    congr 4
    ring
  rw [he theta] at hbound
  apply (hbound.trans (mul_le_mul_of_nonneg_left hs P.profileBound_pos.le)).trans_eq
  have ht : lineEnvelope (y+t*(z.1-x)) P.width 2 z.2=
      lineEnvelope (y-t*x) P.width 2 (z.2-t*z.1) := by
    unfold lineEnvelope
    congr 4
    ring
  change P.profileBound*((2:ℝ)^2*(lineEnvelope x (P.length q.1) 2 z.1*
      lineEnvelope (y+t*(z.1-x)) P.width 2 z.2))=
    (4*P.profileBound)*(lineEnvelope x (P.length q.1) 2 z.1*
      lineEnvelope (y-t*x) P.width 2 (z.2-t*z.1))
  rw [ht]
  ring

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
