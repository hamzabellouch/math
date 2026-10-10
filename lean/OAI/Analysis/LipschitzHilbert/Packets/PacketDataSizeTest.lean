import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensity

namespace OAI

/-! Actual unsigned size tests for unrestricted packet families. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def unsignedSizeTestEnergy (w cb : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (R : Finset P.PacketIndex) (T : SlopeBox) : ℝ :=
  ∑ q∈R, if P.length q.1≤T.length ∧
    (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2) ∧
    T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) ∧
    cb*w/P.length q.1≤|T.slope-P.rowSlope q.1 q.2.1| then
    ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0

theorem unsignedSizeTestEnergy_mono (w cb : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    {R S : Finset P.PacketIndex} (hRS : R⊆S) (T : SlopeBox) :
    P.unsignedSizeTestEnergy w cb cell grid c R T≤P.unsignedSizeTestEnergy w cb cell grid c S T := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hRS
  intro q _ _
  split_ifs
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos q.1).le) P.width_pos.le
  · exact le_rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
