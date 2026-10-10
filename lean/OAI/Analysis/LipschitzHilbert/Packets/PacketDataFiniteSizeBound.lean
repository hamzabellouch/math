import OAI.Analysis.LipschitzHilbert.Geometry.PacketDataTwoSidedSelection

namespace OAI

/-! Every finite packet collection has a finite initial unsigned size.
This starts the threshold algorithm without an additional size premise. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem unsignedSizeTestEnergy_le_coefficient_sum (w cb : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (packets : Finset P.PacketIndex) (T : SlopeBox) (hwidth : T.width=P.width) :
    P.unsignedSizeTestEnergy w cb cell grid c packets T≤
      (∑ q∈packets, ‖c q.1 q.2.1 q.2.2‖^2)*T.area := by
  classical
  unfold unsignedSizeTestEnergy
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro q _
  split_ifs with h
  · rw [SlopeBox.area,hwidth]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h.1 (sq_nonneg _)) P.width_pos.le
  · exact mul_nonneg (sq_nonneg _) T.area_pos.le

theorem exists_finite_unsigned_size_bound (w cb : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (packets : Finset P.PacketIndex) :
    ∃ sigma : ℝ, 0≤sigma ∧ ∀ T : SlopeBox, T.width=P.width →
      P.unsignedSizeTestEnergy w cb cell grid c packets T≤sigma^2*T.area := by
  let B := ∑ q∈packets, ‖c q.1 q.2.1 q.2.2‖^2
  have hB : 0≤B := Finset.sum_nonneg (fun q _ => sq_nonneg _)
  refine ⟨Real.sqrt B,Real.sqrt_nonneg B,?_⟩
  intro T hT
  rw [Real.sq_sqrt hB]
  exact P.unsignedSizeTestEnergy_le_coefficient_sum w cb cell grid c packets T hT

end LipschitzHilbert.PacketLatticeData

end

end OAI
