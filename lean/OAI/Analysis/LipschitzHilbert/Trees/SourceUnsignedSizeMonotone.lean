import OAI.Analysis.LipschitzHilbert.Geometry.SourceTwoSidedSizeSelection

namespace OAI

/-! Unsigned size decreases under removing packets. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem unsignedSizeTestEnergy_mono (w cb : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    {R S : Finset P.PacketIndex} (hRS : R⊆S) (T : SlopeBox) :
    P.unsignedSizeTestEnergy w cb cell grid c R T≤P.unsignedSizeTestEnergy w cb cell grid c S T := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hRS
  intro q _ _
  split_ifs
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos q.1).le) P.width_pos.le
  · exact le_rfl

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
