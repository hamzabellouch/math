import OAI.NumberTheory.Ostmann.Preliminaries.SummandSqrtUpper

namespace OAI

/-! # Prime coverage gives the matching lower bound for each summand -/

namespace Ostmann

open Filter

 theorem EventuallyPrimeSumset.summand_sqrt_lower {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * Real.sqrt (N : ℝ) / Real.log (N : ℝ) ^ 3 ≤ ((summandPrefix A N).card : ℝ) := by
  obtain ⟨C, hC, hupper⟩ := h.symm.summand_sqrt_upper hA
  refine ⟨1 / (4 * C), by positivity, ?_⟩
  filter_upwards [hupper, h.coverage_product_lower, eventually_ge_atTop (2 : ℕ)]
    with N hu hl hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNp
  let a : ℝ := (summandPrefix A N).card
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hh : (N : ℝ) ≤ a * (C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2) *
      (4 * Real.log (N : ℝ)) :=
    (div_le_iff₀ (by positivity : 0 < 4 * Real.log (N : ℝ))).mp
      (hl.trans (mul_le_mul_of_nonneg_left hu ha))
  have hc : Real.sqrt (N : ℝ) ≤ 4 * C * a * Real.log (N : ℝ) ^ 3 := by
    apply (mul_le_mul_iff_right₀ hroot).mp
    calc
      Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = N := by nlinarith [Real.sq_sqrt hNp.le]
      _ ≤ _ := hh
      _ = Real.sqrt (N : ℝ) * (4 * C * a * Real.log (N : ℝ) ^ 3) := by ring
  change (1 / (4 * C)) * Real.sqrt (N : ℝ) / Real.log (N : ℝ) ^ 3 ≤ a
  apply (div_le_iff₀ (pow_pos hlog 3)).mpr
  rw [one_div, inv_mul_eq_div]
  apply (div_le_iff₀ (by positivity : 0 < 4 * C)).mpr
  nlinarith [hc]

end Ostmann

end OAI
