import OAI.NumberTheory.Ostmann.Arithmetic.CompositeSquareRootsLCM
import OAI.NumberTheory.Ostmann.Arithmetic.DivisorGrowthTotient

namespace OAI

namespace Ostmann.Arithmetic

theorem density_le_two_divisors_sq (n k : ℕ) (hn : 0 < n)
    (hk : k ≤ 2 * n.divisors.card) :
    (k : ℝ) / n.totient ≤ 2 * (n.divisors.card : ℝ) ^ 2 / n := by
  have ht : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (k : ℝ) ≤ 2 * n.divisors.card := by exact_mod_cast hk
  have hφ : (n : ℝ) ≤ n.totient * n.divisors.card := by
    exact_mod_cast self_le_totient_mul_divisors n hn
  apply (div_le_div_iff₀ ht hnR).mpr
  calc
    (k : ℝ) * n ≤ (2 * n.divisors.card) * n :=
      mul_le_mul_of_nonneg_right hkR hnR.le
    _ ≤ (2 * n.divisors.card) * (n.totient * n.divisors.card) :=
      mul_le_mul_of_nonneg_left hφ (by positivity)
    _ = (2 * (n.divisors.card : ℝ) ^ 2) * n.totient := by ring

theorem density_le_rpow_of_le_two_divisors (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 0 < n → k ≤ 2 * n.divisors.card →
      (k : ℝ) / n.totient ≤ C * (n : ℝ) ^ (ε - 1) := by
  obtain ⟨C, hC, hbound⟩ := divisors_card_pow_le_rpow 2 ε hε
  refine ⟨2 * C, by positivity, fun n k hn hk => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (k : ℝ) / n.totient ≤ 2 * (n.divisors.card : ℝ) ^ 2 / n :=
      density_le_two_divisors_sq n k hn hk
    _ ≤ 2 * (C * (n : ℝ) ^ ε) / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound n hn) (by norm_num)) hnR.le
    _ = (2 * C) * (n : ℝ) ^ (ε - 1) := by
      rw [Real.rpow_sub hnR, Real.rpow_one]
      ring

theorem unit_square_fiber_density_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ [NeZero n], ∀ a : (ZMod n)ˣ,
      (Nat.card {x : (ZMod n)ˣ // x ^ 2 = a} : ℝ) / Nat.card (ZMod n)ˣ ≤
        C * (n : ℝ) ^ (ε - 1) := by
  classical
  obtain ⟨C, hC, hbound⟩ := density_le_rpow_of_le_two_divisors ε hε
  refine ⟨C, hC, fun n _ a => ?_⟩
  have hc : Nat.card (ZMod n)ˣ = n.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rw [hc]
  exact hbound n _ (NeZero.pos n) (card_unit_square_fiber_le_two_divisors n a)

theorem lcm_unit_square_fiber_density_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, ∀ [NeZero (m.lcm n)],
      ∀ a : (ZMod m × ZMod n)ˣ,
      (Nat.card {x : (ZMod (m.lcm n))ˣ // (lcmUnitsMap m n x) ^ 2 = a} : ℝ) /
        Nat.card (ZMod (m.lcm n))ˣ ≤ C * (m.lcm n : ℝ) ^ (ε - 1) := by
  classical
  obtain ⟨C, hC, hbound⟩ := density_le_rpow_of_le_two_divisors ε hε
  refine ⟨C, hC, fun m n _ a => ?_⟩
  have hc : Nat.card (ZMod (m.lcm n))ˣ = (m.lcm n).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rw [hc]
  exact hbound (m.lcm n) _ (NeZero.pos _) (card_lcm_unit_square_fiber_le_two_divisors m n a)

end Ostmann.Arithmetic

end OAI
