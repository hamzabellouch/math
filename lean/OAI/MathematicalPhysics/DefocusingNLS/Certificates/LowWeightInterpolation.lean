import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingLowerWeightBound

namespace OAI

/-! # Uniform interpolation of the lower Bessel weight against mass -/

namespace DefocusingNLS

theorem lowBesselWeight_interpolation (a k ε : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x r : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ r →
      (x + r ^ 2) ^ (6 - a) ≤ ε * r ^ (2 * k) + C := by
  let D : ℝ := 2 ^ (6 - a)
  have hD : 0 < D := Real.rpow_pos_of_pos (by norm_num) _
  let R := max 1 (D / ε)
  have hR : 1 ≤ R := le_max_left _ _
  have hRp : 0 < R := by linarith
  refine ⟨(1 + R ^ 2) ^ (6 - a), by positivity, ?_⟩
  intro x r hx hx1 hr
  by_cases hsmall : r ≤ R
  · have hr2 : r ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr hsmall 2
    exact (Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)).trans
      (le_add_of_nonneg_left (mul_nonneg hε.le (Real.rpow_nonneg hr _)))
  · have hlarge : R ≤ r := (lt_of_not_ge hsmall).le
    have hr1 : 1 ≤ r := hR.trans hlarge
    have hrp : 0 < r := by linarith
    have hi : D * r⁻¹ ≤ ε := by
      have hd : D / ε ≤ r := (le_max_right _ _).trans hlarge
      have he : D ≤ ε * r := by simpa only [mul_comm] using (div_le_iff₀ hε).mp hd
      exact (div_le_iff₀ hrp).mpr (by simpa only [div_eq_mul_inv, mul_comm] using he)
    have hr2 : 1 ≤ r ^ 2 := by nlinarith
    calc
      (x + r ^ 2) ^ (6 - a) ≤ (2 * r ^ 2) ^ (6 - a) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ = D * r ^ (2 * (6 - a)) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg r),
          ← Real.rpow_natCast, ← Real.rpow_mul hr]
        norm_num [D]
      _ = D * (r ^ (2 * k) * r ^ (2 * (6 - a) - 2 * k)) := by
        rw [← Real.rpow_add hrp]
        congr 2
        ring
      _ ≤ D * (r ^ (2 * k) * r ^ (-1 : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)) (Real.rpow_nonneg hr _)) hD.le
      _ = r ^ (2 * k) * (D * r⁻¹) := by rw [Real.rpow_neg_one]; ring
      _ ≤ r ^ (2 * k) * ε := mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg hr _)
      _ ≤ ε * r ^ (2 * k) + (1 + R ^ 2) ^ (6 - a) := by
        nlinarith [Real.rpow_nonneg (show 0 ≤ 1 + R ^ 2 by positivity) (6 - a)]

end DefocusingNLS

end OAI
