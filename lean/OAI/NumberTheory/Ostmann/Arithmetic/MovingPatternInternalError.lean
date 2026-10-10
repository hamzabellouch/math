import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGiantVariation
import OAI.NumberTheory.Ostmann.Arithmetic.MovingArithmeticSumRate

namespace OAI

/-! # The internal-prime error for the literal moving pattern cost -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

/-- All internal class counts and moving windows share the same eventual
error bound. Only the original point-mass bounds on the priors are used. -/
theorem movingPattern_internal_arithmetic_error_rate (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin B D E : ℝ) (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hE : 0 ≤ E) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (p : Fin m → ℕ) (c : ℕ) (U α β amp lo hi : ℝ),
      c ≤ 4 * n * 2 ^ n → 1 ≤ U →
      Real.log U ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      0 ≤ α → α ≤ Real.exp (E * L - Real.exp ((39 / 10000 : ℝ) * L)) →
      0 ≤ β → β ≤ Real.exp (E * L - Real.exp ((1 / 100 : ℝ) * L)) →
      0 ≤ amp → amp ≤ 4 → lo ≤ hi → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      ((amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2) *
        movingInternalArithmeticError n c (2 ^ n * (r₀ + m + 4 * n + 4))
          (Real.exp (A * m)) U α β (Real.exp ((1 / 100 : ℝ) * L)) ≤
        Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  obtain ⟨C, hC, hcost⟩ := movingPattern_pointwise_cost_budget ψ n r₀ k A Wwin B D hA hWwin
  let H : ℝ := (2 ^ n : ℕ) * ((r₀ + 4 * n + 4 : ℕ) + (k : ℝ) ^ 4)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hAk : 0 ≤ A * (k : ℝ) ^ 4 := by positivity
  filter_upwards [moving_internal_error_with_cost n (4 * n * 2 ^ n)
    (A * (k : ℝ) ^ 4) H E 1 C hAk hH hE (by norm_num) (by linarith),
    eventually_ge_atTop (1 : ℝ)] with L herr hL
  dsimp only
  intro p c U α β amp lo hi hc hU hUlog hα0 hα hβ0 hβ hamp0 hamp hhi hwidth hp
  let m := spectatorBulkCount k L
  let d := 2 ^ n * (r₀ + m + 4 * n + 4)
  let F := Real.exp (A * m)
  have hL0 : 0 ≤ L := by linarith
  have hm := spectatorBulkCount_upper k L hL0
  have hF : 1 ≤ F := Real.one_le_exp_iff.mpr (mul_nonneg hA (Nat.cast_nonneg _))
  have hFreq : Real.log F ≤ A * (k : ℝ) ^ 4 * L := by
    rw [Real.log_exp]
    nlinarith [mul_le_mul_of_nonneg_left hm hA]
  have hdeg : (d : ℝ) ≤ H * L := by
    dsimp only [d, H]
    push_cast
    have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ (2 : ℝ) ^ n by positivity)
    have hbase := mul_le_mul_of_nonneg_left hL (show 0 ≤ (2 : ℝ) ^ n * (r₀ + 4 * n + 4) by positivity)
    nlinarith
  have hs := herr d F U α β hF hU hα0 hα hβ0 hFreq hdeg hUlog hβ
  have hmono := movingInternalArithmeticError_mono_card n c (4 * n * 2 ^ n) d F U α β
    (Real.exp ((1 / 100 : ℝ) * L)) hc hF hU hα0 hβ0 (Real.exp_nonneg _)
  have he0 := movingInternalArithmeticError_nonneg n (4 * n * 2 ^ n) d F U α β
    (Real.exp ((1 / 100 : ℝ) * L)) hF hU hα0 hβ0 (Real.exp_nonneg _)
  let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
    (movingFourierVariationBudget ψ F lo hi n *
      (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  have hcost0 : 0 ≤ cost := by dsimp only [cost]; positivity
  have hprod : (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 = ∏ i, (p i : ℝ) ^ (2 ^ (n + 1)) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, pow_succ]
  have hcb : cost ≤ Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
    apply le_trans _ (hcost L hL p F lo hi (Real.exp_nonneg _) le_rfl hhi hwidth hp)
    rw [hprod]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hamp (Finset.prod_nonneg fun _ _ => by positivity))
      (sq_nonneg _)
  have hbudget : (1 : ℝ) ≤ (2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
      (max 2 (Real.exp ((1 : ℝ) * L))) ^ (4 * n * 2 ^ n) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (one_le_pow₀ (le_trans (by norm_num) (le_max_left _ _)))
  have hcb' := hcb.trans (le_mul_of_one_le_left (Real.exp_nonneg _) hbudget)
  exact ((mul_le_mul_of_nonneg_left hmono hcost0).trans
    (mul_le_mul_of_nonneg_right hcb' he0)).trans hs

end Ostmann

end OAI
