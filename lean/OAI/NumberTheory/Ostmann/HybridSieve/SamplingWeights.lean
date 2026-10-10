import OAI.NumberTheory.Ostmann.HybridSieve.CharacterFamily

namespace OAI

open scoped BigOperators
namespace Ostmann.HybridSieve

theorem one_le_familyWeight {Q : ℕ} (i : PrimitiveFamily Q) : 1 ≤ familyWeight i := by
  have ht : (0 : ℝ) < (i.1.val + 1).totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.succ_pos i.1.val)
  unfold familyWeight
  apply (one_le_div ht).mpr
  exact_mod_cast Nat.totient_le (i.1.val + 1)

theorem unweighted_energy_le_family_weighted {ι : Type*} [Fintype ι] {Q : ℕ}
    (character : ι → PrimitiveFamily Q) (f : ι → ℂ) :
    (∑ j, ‖f j‖ ^ 2) ≤ ∑ j, familyWeight (character j) * ‖f j‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro j hj
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (one_le_familyWeight (character j)) (sq_nonneg ‖f j‖)

end Ostmann.HybridSieve

end OAI
