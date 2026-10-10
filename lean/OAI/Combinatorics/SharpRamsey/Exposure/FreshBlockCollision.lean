import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.FreshBlockBudgets

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {B X ι : Type*} [Fintype B] [Fintype X] [Fintype ι] [DecidableEq B] [DecidableEq ι]

theorem collision_all_indices (e : B×X ↪ ι) (own : ι→Option B) (c : ι→ι→ℝ≥0) :
    (Fintype.card X:ℝ)*(∑ f : B→X,∑ i,
      (maximumCharge c i (otherRepresentatives e own f i):ℝ))≤
      (Fintype.card (B→X):ℝ)*∑ i,∑ j,(c i j:ℝ) := by
  calc
    _ ≤ (Fintype.card X:ℝ)*(∑ f : B→X,∑ i,
        ∑ j∈freshRepresentatives e f,(c i j:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro f _
      apply sum_le_sum
      intro i _
      exact (maximumCharge_le_sum c i _).trans
        (sum_le_sum_of_subset_of_nonneg (otherRepresentatives_sub e own f i)
          (fun j _ _ => NNReal.coe_nonneg (c i j)))
    _ = ∑ i,(Fintype.card X:ℝ)*(∑ f : B→X,
        ∑ j∈freshRepresentatives e f,(c i j:ℝ)) := by rw [sum_comm,mul_sum]
    _ ≤ ∑ i,(Fintype.card (B→X):ℝ)*∑ j,(c i j:ℝ) := by
      apply sum_le_sum
      intro i _
      exact selected_fixed_observable e (fun j => (c i j:ℝ)) (fun j => (c i j).coe_nonneg)
    _ = _ := by rw [mul_sum]

theorem collision_selected_indices (e : B×X ↪ ι) (own : ι→Option B)
    (hown : ∀ b x,own (e (b,x))=some b) (c : ι→ι→ℝ≥0) :
    (Fintype.card X:ℝ)^2*(∑ f : B→X,∑ i∈freshRepresentatives e f,
      (maximumCharge c i (otherRepresentatives e own f i):ℝ))≤
      (Fintype.card (B→X):ℝ)*∑ i,∑ j,(c i j:ℝ) := by
  have hh := mul_le_mul_of_nonneg_left (selected_charge_absorption e own hown c)
    (Nat.cast_nonneg (Fintype.card X) : (0:ℝ)≤Fintype.card X)
  rw [← mul_assoc,←sq] at hh
  exact hh.trans (collision_all_indices e own c)

end
end SharpLogRamsey.Selection

end

end OAI
