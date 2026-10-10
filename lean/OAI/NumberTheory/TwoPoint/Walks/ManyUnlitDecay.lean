import OAI.NumberTheory.TwoPoint.Bounds.LitOccurrenceWeights
import OAI.NumberTheory.TwoPoint.Walks.RankDecay

namespace OAI

/-! The extra reciprocal powers of many unlit occurrences beat every crude cost. -/

namespace TwoPointCorrelations

open Filter

/-- Here `E` is the number of extra reciprocal powers. The bound
`L^(1/50) ≤ 2E` follows from the exact nonsingleton count. -/
theorem eventually_many_unlit_decay (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : ℕ) (H : ℝ),
      L ^ (1 / 50 : ℝ) ≤ 2 * E → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      Real.exp (C * L * (Real.log L) ^ 2) * (H⁻¹) ^ E ≤
        Real.exp (-L ^ (101 / 100 : ℝ)) := by
  have hgap := (tendsto_rpow_atTop (show 0 < (1 / 200 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop 4)
  filter_upwards [eventually_ge_atTop 1, eventually_crude_cost_small C hC, hgap]
    with L hL hcost hgap
  intro E H hE hH
  have hLp : 0 < L := by linarith
  have hHp : 0 < H := (Real.exp_pos _).trans_le hH
  have hinv : H⁻¹ ≤ Real.exp (-L ^ (199 / 200 : ℝ)) := by
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos _) hH
  have hextra := mul_le_mul_of_nonneg_right hE
    (Real.rpow_nonneg hLp.le (199 / 200 : ℝ))
  have heq : L ^ (1 / 50 : ℝ) * L ^ (199 / 200 : ℝ) = L ^ (203 / 200 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  rw [heq] at hextra
  have hgap' := mul_le_mul_of_nonneg_left hgap
    (Real.rpow_nonneg hLp.le (101 / 100 : ℝ))
  have heq' : L ^ (101 / 100 : ℝ) * L ^ (1 / 200 : ℝ) = L ^ (203 / 200 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  rw [heq'] at hgap'
  calc
    _ ≤ Real.exp (C * L * (Real.log L) ^ 2) *
        (Real.exp (-L ^ (199 / 200 : ℝ))) ^ E :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr hHp.le) hinv E)
        (Real.exp_pos _).le
    _ = Real.exp (C * L * (Real.log L) ^ 2 - (E : ℝ) * L ^ (199 / 200 : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.rpow_nonneg hLp.le (203 / 200 : ℝ)]

/-- Transfer a finite designated-term estimate, with its complete crude
weight retained, to the many-unlit negligible bound. -/
theorem eventually_many_unlit_total (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (U E : ℕ) (H cost total : ℝ),
      L ^ (1 / 50 : ℝ) < U → U ≤ 2 * E →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      cost ≤ Real.exp (C * L * (Real.log L) ^ 2) →
      total ≤ cost * (H⁻¹) ^ E →
      total ≤ Real.exp (-L ^ (101 / 100 : ℝ)) := by
  filter_upwards [eventually_many_unlit_decay C hC] with L hdecay
  intro U E H cost total hU hUE hH hcost htotal
  have hE : L ^ (1 / 50 : ℝ) ≤ 2 * E := by
    have hUE' : (U : ℝ) ≤ 2 * E := by exact_mod_cast hUE
    linarith
  have hHp : 0 < H := (Real.exp_pos _).trans_le hH
  exact htotal.trans ((mul_le_mul_of_nonneg_right hcost
    (pow_nonneg (inv_nonneg.mpr hHp.le) E)).trans (hdecay E H hE hH))

end TwoPointCorrelations

end OAI
