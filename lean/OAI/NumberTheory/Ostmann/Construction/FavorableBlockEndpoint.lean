import OAI.NumberTheory.Ostmann.Construction.FavorableGiantCutoff
import OAI.NumberTheory.Ostmann.Construction.OneSidedDecayBudget
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticErrorRates

namespace OAI

/-! # An integral endpoint chosen after the favorable logarithmic block -/
namespace Ostmann
open Filter

/-- Rounding the endpoint up changes its logarithm by at most one. The reserve
in the block leaves every giant-cell prime below the collision cutoff. -/
theorem eventual_favorable_block_endpoint (k : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ lo : ℝ,
      Real.exp ((5 / 100 : ℝ) * L) ≤ lo → lo ≤ Real.exp ((9 / 10 : ℝ) * L) →
      ∃ Y : ℝ, ∃ hi : ℕ, (hi : ℝ) = Real.exp Y ∧
        2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y ∧
        Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 ∧
        Real.exp ((4 / 100 : ℝ) * L) ≤ Y ∧ Y ≤ Real.exp L ∧
        ⌈Real.exp (lo + 10 * Real.exp ((1 / 100 : ℝ) * L) + 3)⌉₊ ≤
          tailCollisionCutoff Y := by
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (eventual_tailCollisionCutoff 0)
  have ht : Tendsto (fun L : ℝ => Real.exp ((4 / 100 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [arithmetic_exponent_absorption (9 / 10) 1 0
      (3 + 24 * (2 : ℝ) ^ k) 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventual_polynomial_log_budget (8 + |Real.log 2|) 1 (1 / 100) 1 1
      (by positivity) (by norm_num) (by norm_num) (by norm_num),
    ht.eventually (eventually_ge_atTop X₀), eventually_ge_atTop (1 : ℝ)]
    with L hupp hmargin hlarge hL lo hlo hhi
  have hpow : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  let t := 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L))
  have hlo0 : 0 < lo := (Real.exp_pos _).trans_le hlo
  have ht0 : 0 < t := by dsimp [t]; positivity
  let hi := ⌈Real.exp t⌉₊
  have hhi0 : (0 : ℝ) < hi := (Real.exp_pos t).trans_le (Nat.le_ceil _)
  have hroundlo : t ≤ Real.log (hi : ℝ) := by
    rw [Real.le_log_iff_exp_le hhi0]
    exact Nat.le_ceil _
  have hroundhi : Real.log (hi : ℝ) ≤ t + 1 := by
    apply (Real.log_le_iff_le_exp hhi0).mpr
    have hc := Nat.ceil_lt_add_one (Real.exp_nonneg t)
    change (hi : ℝ) < Real.exp t + 1 at hc
    have he := Real.add_one_le_exp (1 : ℝ)
    have hte : 1 ≤ Real.exp t := Real.one_le_exp ht0.le
    rw [Real.exp_add]
    nlinarith
  have hYlo : Real.exp ((4 / 100 : ℝ) * L) ≤ Real.log (hi : ℝ) := by
    have hh : Real.exp ((4 / 100 : ℝ) * L) ≤ lo :=
      (Real.exp_le_exp.mpr (by linarith)).trans hlo
    dsimp [t] at hroundlo
    have hp : 0 ≤ (2 : ℝ) ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) := by positivity
    linarith
  have hYhi : Real.log (hi : ℝ) ≤ Real.exp L := by
    have hh : Real.exp ((1 / 100 : ℝ) * L) ≤ Real.exp ((9 / 10 : ℝ) * L) :=
      Real.exp_le_exp.mpr (by linarith)
    have he : 1 ≤ Real.exp ((9 / 10 : ℝ) * L) := Real.one_le_exp (by linarith)
    simp only [pow_one, zero_mul, Real.exp_zero, one_mul] at hupp
    dsimp [t] at hroundhi
    rw [pow_succ] at hroundhi
    have hp := mul_le_mul_of_nonneg_left hh (show 0 ≤ 24 * (2 : ℝ) ^ k by positivity)
    have hLmul := mul_le_mul_of_nonneg_left hL
      (show 0 ≤ (3 + 24 * (2 : ℝ) ^ k) * Real.exp ((9 / 10 : ℝ) * L) by positivity)
    have hC : 0 ≤ (3 + 24 * (2 : ℝ) ^ k) * L := mul_nonneg (by positivity) (by linarith)
    nlinarith only [hroundhi, hhi, he, hp, hLmul, hupp, hC]
  have hcut := hX₀ _ (hlarge.trans hYlo)
  have hQ := tailCollisionCutoff_bounds _ hcut.1 hcut.2.1
  have hlogY : Real.log (Real.log (hi : ℝ)) ≤ L := by
    apply (Real.log_le_iff_le_exp ((Real.exp_pos _).trans_le hYlo)).mpr hYhi
  have hm := hmargin L (by linarith) (by simp)
  simp only [pow_one, one_mul] at hm
  have hmargin' : 5 * L + Real.log 2 + 3 ≤ Real.exp ((1 / 100 : ℝ) * L) := by
    have hab := le_abs_self (Real.log 2)
    have ha0 := abs_nonneg (Real.log 2)
    nlinarith
  have hlogcut : lo + 10 * Real.exp ((1 / 100 : ℝ) * L) + 3 ≤
      Real.log (tailCollisionCutoff (Real.log (hi : ℝ)) : ℝ) := by
    dsimp [t] at hroundlo
    rw [pow_succ] at hroundlo
    have hp := mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg ((1 / 100 : ℝ) * L))
    nlinarith only [hQ.2.2, hlogY, hmargin', hroundlo, hp,
      Real.exp_nonneg ((1 / 100 : ℝ) * L)]
  refine ⟨Real.log (hi : ℝ), hi, (Real.exp_log hhi0).symm,
    hroundlo, hroundhi, hYlo, hYhi, ?_⟩
  apply Nat.ceil_le.mpr
  have hQ0 : (0 : ℝ) < tailCollisionCutoff (Real.log (hi : ℝ)) := by exact_mod_cast hQ.1
  simpa only [Real.exp_log hQ0] using Real.exp_le_exp.mpr hlogcut

end Ostmann

end OAI
