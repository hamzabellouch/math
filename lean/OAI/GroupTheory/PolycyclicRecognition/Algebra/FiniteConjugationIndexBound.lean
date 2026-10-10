import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteKernelSolvable
import Mathlib.Data.Fintype.Card

namespace OAI

/-! # A uniform bound for centralizing a finite normal subgroup -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem finite_normal_centralizer_index_le (N : Subgroup G) [N.Normal] [Finite N]
    (b : ℕ) (hb : Nat.card N ≤ b) :
    (Subgroup.centralizer (N : Set G)).index ≤ b ^ b := by
  have hp : 0 < b := lt_of_lt_of_le Nat.card_pos hb
  have hA : Nat.card (MulAut N) ≤ Nat.card N ^ Nat.card N := by
    have h := Nat.card_le_card_of_injective (fun a : MulAut N => (a : N → N))
      DFunLike.coe_injective
    simpa only [Nat.card_fun] using h
  rw [← conjugation_ker_eq_centralizer N, Subgroup.index_ker]
  exact (Nat.card_le_card_of_injective _ Subtype.val_injective).trans
    (hA.trans ((Nat.pow_le_pow_left hb _).trans (Nat.pow_le_pow_right hp hb)))

end PolycyclicRecognition

end

end OAI
