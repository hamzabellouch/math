import OAI.Combinatorics.BalancedRyser.Local.ReuseExtensionTable

namespace OAI

namespace Balanced
open scoped _root_.Balanced

theorem reuse_extension_exponent_le : ∀ old : Finset (Fin 4),
    (4 - (old.card : ℤ)) +
        (if (fixedGeneratorPositions old).card = 0 then (1 : ℤ) else 0) -
        (4 - ((fixedGeneratorPositions old).card : ℤ)) - 1 ≤
      -(reuseSaving old.card : ℤ) := by
  decide

theorem reuse_extension_scale_le (q : ℝ) (hq : 1 ≤ q) (old : Finset (Fin 4)) :
    q ^ (4 - old.card) *
        (if (fixedGeneratorPositions old).card = 0 then q else 1) /
        q ^ (4 - (fixedGeneratorPositions old).card) / q ≤
      1 / q ^ reuseSaving old.card := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hq)
  have hj : old.card ≤ 4 := by simpa using Finset.card_le_univ old
  have hf : (fixedGeneratorPositions old).card ≤ 4 := by
    simpa using Finset.card_le_univ (fixedGeneratorPositions old)
  have hjcast : (4 : ℤ) - (old.card : ℤ) = ((4 - old.card : ℕ) : ℤ) :=
    (Int.ofNat_sub hj).symm
  have hfcast : (4 : ℤ) - ((fixedGeneratorPositions old).card : ℤ) =
      ((4 - (fixedGeneratorPositions old).card : ℕ) : ℤ) :=
    (Int.ofNat_sub hf).symm
  calc
    q ^ (4 - old.card) *
        (if (fixedGeneratorPositions old).card = 0 then q else 1) /
        q ^ (4 - (fixedGeneratorPositions old).card) / q =
      q ^ ((4 - (old.card : ℤ)) +
        (if (fixedGeneratorPositions old).card = 0 then (1 : ℤ) else 0) -
        (4 - ((fixedGeneratorPositions old).card : ℤ)) - 1) := by
      rw [hjcast, hfcast, zpow_sub₀ hq0, zpow_sub₀ hq0, zpow_add₀ hq0]
      simp only [zpow_natCast, zpow_one]
      split_ifs <;> simp
    _ ≤ q ^ (-(reuseSaving old.card : ℤ)) :=
      zpow_le_zpow_right₀ hq (reuse_extension_exponent_le old)
    _ = 1 / q ^ reuseSaving old.card := by
      simp [zpow_neg, div_eq_mul_inv]

theorem reuse_extension_scale_mul_le (q K : ℝ) (hq : 1 ≤ q) (hK : 0 ≤ K)
    (old : Finset (Fin 4)) :
    K * (q ^ (4 - old.card) *
        (if (fixedGeneratorPositions old).card = 0 then q else 1) /
        q ^ (4 - (fixedGeneratorPositions old).card) / q) ≤
      K / q ^ reuseSaving old.card := by
  have h := mul_le_mul_of_nonneg_left (reuse_extension_scale_le q hq old) hK
  simpa only [mul_one_div] using h

end Balanced

end OAI
