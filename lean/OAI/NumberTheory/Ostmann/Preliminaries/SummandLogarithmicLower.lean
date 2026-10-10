import OAI.NumberTheory.Ostmann.Preliminaries.SummandCoverageLower
import OAI.NumberTheory.Ostmann.Preliminaries.SummandLogarithmicUpper

namespace OAI

/-! # Every fixed logarithmic power is a lower bound for either summand -/

namespace Ostmann

open Filter

 theorem EventuallyPrimeSumset.summand_logarithmic_lower {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (k : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * Real.log (N : ℝ) ^ k ≤ ((summandPrefix A N).card : ℝ) := by
  obtain ⟨C, hC, hupper⟩ := h.symm.summand_logarithmic_upper hA (k + 1) (by omega)
  refine ⟨1 / (4 * C), by positivity, ?_⟩
  filter_upwards [hupper, h.coverage_product_lower, eventually_ge_atTop (2 : ℕ)]
    with N hu hl hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  let a : ℝ := (summandPrefix A N).card
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hx : (N : ℝ) / (4 * Real.log (N : ℝ)) ≤
      a * (C * N / Real.log (N : ℝ) ^ (k + 1)) :=
    hl.trans (mul_le_mul_of_nonneg_left hu ha)
  simp only [← mul_div_assoc] at hx
  have hy := (div_le_div_iff₀ (by positivity : 0 < 4 * Real.log (N : ℝ))
    (pow_pos hlog (k + 1))).mp hx
  have hz : ((N : ℝ) * Real.log (N : ℝ)) * Real.log (N : ℝ) ^ k ≤
      ((N : ℝ) * Real.log (N : ℝ)) * (4 * C * a) := by
    calc
      _ = (N : ℝ) * Real.log (N : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
      _ ≤ _ := hy
      _ = _ := by ring
  have hh := (mul_le_mul_iff_right₀ (mul_pos hNp hlog)).mp hz
  change (1 / (4 * C)) * Real.log (N : ℝ) ^ k ≤ a
  rw [one_div, inv_mul_eq_div]
  exact (div_le_iff₀ (by positivity : 0 < 4 * C)).mpr (by nlinarith [hh])

end Ostmann

end OAI
