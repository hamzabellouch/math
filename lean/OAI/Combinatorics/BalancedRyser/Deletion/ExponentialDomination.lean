import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OAI

open Filter
open scoped Topology

namespace BalancedRyser

theorem deletion_ratio_exponential_envelope
    {a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K)
    {q : ℕ} (hq : 1 ≤ q) :
    a⁻¹ * K ^ (2 * (q + 1)) ≤
      Real.exp ((a⁻¹ + 4 * K) * (q : ℝ)) := by
  have ha' : 0 ≤ a⁻¹ := le_of_lt (inv_pos.mpr ha)
  have hq' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqa : a⁻¹ ≤ a⁻¹ * (q : ℝ) := by nlinarith
  have hpow : K ^ (2 * (q + 1)) ≤
      Real.exp K ^ (2 * (q + 1)) :=
    pow_le_pow_left₀ hK (by linarith [Real.add_one_le_exp K]) _
  have hinv : a⁻¹ ≤ Real.exp a⁻¹ := by
    linarith [Real.add_one_le_exp a⁻¹]
  calc
    a⁻¹ * K ^ (2 * (q + 1)) ≤
        Real.exp a⁻¹ * Real.exp K ^ (2 * (q + 1)) :=
      mul_le_mul hinv hpow (pow_nonneg hK _) (Real.exp_nonneg _)
    _ = Real.exp (a⁻¹ + (2 * (q + 1) : ℕ) * K) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp ((a⁻¹ + 4 * K) * (q : ℝ)) := by
      apply Real.exp_monotone
      push_cast
      nlinarith

theorem deletion_ratio_exponential_coefficient_pos
    {a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K) :
    0 < a⁻¹ + 4 * K := by
  positivity

theorem tendsto_exp_linear_mul_exp_neg_mul_log
    (C : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun q : ℕ => Real.exp (C * q) *
      Real.exp (-c * q * Real.log q)) atTop (𝓝 0) := by
  have hn : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun q : ℕ => c * Real.log q + (-C)) atTop atTop :=
    ((Real.tendsto_log_atTop.comp hn).const_mul_atTop hc).atTop_add
      tendsto_const_nhds
  have hp := hn.atTop_mul_atTop₀ hl
  have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hp)
  convert he using 1
  ext q
  rw [← Real.exp_add]
  congr 1
  simp only [Function.comp_apply]
  ring

theorem tendsto_zero_of_exponential_domination
    {p u : ℕ → ℝ} (C : ℝ) {c : ℝ} (hc : 0 < c)
    (hp : ∀ᶠ q in atTop, 0 ≤ p q)
    (hdom : ∀ᶠ q in atTop, p q ≤ Real.exp (C * q) * u q)
    (hsmall : ∀ᶠ q in atTop,
      u q ≤ Real.exp (-c * q * Real.log q)) :
    Tendsto p atTop (𝓝 0) := by
  apply squeeze_zero' hp _ (tendsto_exp_linear_mul_exp_neg_mul_log C hc)
  filter_upwards [hdom, hsmall] with q hd hs
  exact hd.trans (mul_le_mul_of_nonneg_left hs (Real.exp_nonneg _))

end BalancedRyser

end OAI
