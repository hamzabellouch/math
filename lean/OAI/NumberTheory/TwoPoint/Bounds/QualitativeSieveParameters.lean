import OAI.NumberTheory.TwoPoint.Bounds.MertensScale
import OAI.NumberTheory.TwoPoint.Bounds.SieveBoundaryScale

namespace OAI

/-! A small sieve cutoff for the qualitative multiplier. Truncation uses
the same proved finite four-form sieve; its cutoff is chosen so that the
entire CRT boundary cost lies far below the available interval length. -/

namespace TwoPointCorrelations

open Filter

noncomputable def qualitativeSieveHalfOrder (B : ℝ) : ℕ := ⌈500 * Real.log B⌉₊

noncomputable def qualitativeSieveLogCutoff (B : ℝ) : ℝ :=
  B ^ (9999 / 10000 : ℝ) / (100 * (2 * qualitativeSieveHalfOrder B + 1 : ℕ))

lemma qualitativeSieveLogCutoff_le_power (B : ℝ) (hB : 0 ≤ B) :
    qualitativeSieveLogCutoff B ≤ B ^ (9999 / 10000 : ℝ) := by
  apply div_le_self (Real.rpow_nonneg hB _)
  have hr : (0 : ℝ) ≤ qualitativeSieveHalfOrder B := Nat.cast_nonneg _
  push_cast
  nlinarith only [hr]

structure QualitativeSieveParameters (B : ℝ) : Prop where
  log_one : 1 ≤ Real.log B
  nextOrder_large : 220 * Real.log B ≤ (2 * qualitativeSieveHalfOrder B + 1 : ℕ)
  order_small : (2 * qualitativeSieveHalfOrder B : ℕ) ≤ 1002 * Real.log B
  cutoff_one : 1 ≤ qualitativeSieveLogCutoff B
  cutoff_le : qualitativeSieveLogCutoff B ≤ B
  cutoff_cost : qualitativeSieveLogCutoff B * Real.log B ≤
    B ^ (9999 / 10000 : ℝ) / 100000
  inverse_cutoff : 1 / qualitativeSieveLogCutoff B ≤
    100300 * Real.log B / B ^ (9999 / 10000 : ℝ)

theorem eventually_qualitativeSieveParameters :
    ∀ᶠ B : ℝ in atTop, QualitativeSieveParameters B := by
  have hs := (isLittleO_log_rpow_atTop
    (show 0 < (9999 / 10000 : ℝ) by norm_num)).bound
      (show 0 < (1 / 100300 : ℝ) by norm_num)
  filter_upwards [eventually_ge_atTop (Real.exp 1), hs] with B hB hsB
  have hB₁ : 1 ≤ B := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hB
  have hBp : 0 < B := zero_lt_one.trans_le hB₁
  have ht : 1 ≤ Real.log B := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hB
  have hBa : 0 < B ^ (9999 / 10000 : ℝ) := Real.rpow_pos_of_pos hBp _
  have ht₀ : 0 ≤ Real.log B := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg ht₀, Real.norm_eq_abs, abs_of_pos hBa] at hsB
  have hdom : 100300 * Real.log B ≤ B ^ (9999 / 10000 : ℝ) := by linarith
  let r := qualitativeSieveHalfOrder B
  have hrlo : 500 * Real.log B ≤ (r : ℝ) := Nat.le_ceil _
  have hrhi : (r : ℝ) < 500 * Real.log B + 1 := Nat.ceil_lt_add_one (by positivity)
  have hJlo : 1000 * Real.log B ≤ (2 * r + 1 : ℕ) := by push_cast; linarith
  have hJhi : (2 * r + 1 : ℕ) ≤ 1003 * Real.log B := by push_cast; linarith
  have hden : 0 < (100 : ℝ) * (2 * r + 1 : ℕ) := by positivity
  have hden₁ : 1 ≤ (100 : ℝ) * (2 * r + 1 : ℕ) := by
    have hr₀ : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    push_cast
    nlinarith only [hr₀]
  have hX₁ : 1 ≤ qualitativeSieveLogCutoff B := by
    change 1 ≤ B ^ (9999 / 10000 : ℝ) / (100 * (2 * r + 1 : ℕ))
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hJhi, hdom]
  refine ⟨ht, ?_, ?_, hX₁, ?_, ?_, ?_⟩
  · change 220 * Real.log B ≤ (2 * r + 1 : ℕ)
    linarith
  · change (2 * r : ℕ) ≤ 1002 * Real.log B
    push_cast
    linarith
  · calc
      qualitativeSieveLogCutoff B ≤ B ^ (9999 / 10000 : ℝ) :=
        div_le_self hBa.le hden₁
      _ ≤ B := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB₁
          (show (9999 / 10000 : ℝ) ≤ 1 by norm_num)
  · have htdiv : Real.log B / (100 * (2 * r + 1 : ℕ)) ≤ (1 / 100000 : ℝ) := by
      apply (div_le_iff₀ hden).mpr
      nlinarith only [hJlo]
    calc
      qualitativeSieveLogCutoff B * Real.log B =
          B ^ (9999 / 10000 : ℝ) * (Real.log B / (100 * (2 * r + 1 : ℕ))) := by
        unfold qualitativeSieveLogCutoff
        dsimp [r]
        ring
      _ ≤ B ^ (9999 / 10000 : ℝ) * (1 / 100000 : ℝ) :=
        mul_le_mul_of_nonneg_left htdiv hBa.le
      _ = _ := by ring
  · calc
      1 / qualitativeSieveLogCutoff B =
          (100 * (2 * r + 1 : ℕ)) / B ^ (9999 / 10000 : ℝ) := by
        unfold qualitativeSieveLogCutoff
        dsimp [r]
        field_simp [hBa.ne', hden.ne']
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith only [hJhi]) hBa.le

end TwoPointCorrelations

end OAI
