import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Finite
import OAI.NumberTheory.Ostmann.Construction.TransferFrequencyRigidity

namespace OAI

/-! # The manuscript's gaps give both frequency cutoffs and history rigidity -/

namespace Ostmann

open Filter
open scoped Topology

noncomputable def transferErrorScale (Δ m : ℝ) (j : ℕ) : ℝ :=
  (2 : ℝ) ^ j * Δ + 2 * (4 : ℝ) ^ j * Real.sqrt m

/-- The gap for step j+1. -/
noncomputable def transferNextGap (Δ m : ℝ) (j : ℕ) : ℝ :=
  (2 : ℝ) ^ j * Δ + (4 : ℝ) ^ (j + 1) * Real.sqrt m

theorem transfer_gap_minus_error (Δ m : ℝ) (j : ℕ) :
    transferNextGap Δ m j - transferErrorScale Δ m j =
      2 * (4 : ℝ) ^ j * Real.sqrt m := by
  simp only [transferNextGap, transferErrorScale, pow_succ]
  ring

theorem transfer_error_reserve (Δ m : ℝ) (j : ℕ) :
    transferErrorScale Δ m (j + 1) -
        (transferErrorScale Δ m j + transferNextGap Δ m j) =
      2 * (4 : ℝ) ^ j * Real.sqrt m := by
  simp only [transferNextGap, transferErrorScale, pow_succ]
  ring

/-- A single sufficiently-large-m cutoff gives every transfer level its
fixed covering and integer-rounding reserve. -/
theorem eventually_transfer_reserve (C : ℝ) :
    ∀ᶠ m : ℝ in atTop, ∀ Δ : ℝ, ∀ j : ℕ,
      Real.log 4 + 2 * C < transferNextGap Δ m j - transferErrorScale Δ m j ∧
      Real.log 4 + 2 * C < transferErrorScale Δ m (j + 1) -
        (transferErrorScale Δ m j + transferNextGap Δ m j) := by
  filter_upwards [Real.tendsto_sqrt_atTop.eventually (eventually_gt_atTop
    ((Real.log 4 + 2 * C) / 2))] with m hm
  intro Δ j
  have hp : 1 ≤ (4 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hr := Real.sqrt_nonneg m
  have hh : Real.log 4 + 2 * C < 2 * (4 : ℝ) ^ j * Real.sqrt m := by nlinarith
  rw [transfer_gap_minus_error, transfer_error_reserve]
  exact ⟨hh, hh⟩

/-- The positive-product ranges make the determinant gap strict. -/
theorem transfer_integer_rigidity_gap (K B R : ℕ) (T Δ E C : ℝ)
    (hK : (K : ℝ) ≤ Real.exp (T + C)) (hB : (B : ℝ) ≤ Real.exp E)
    (hR : Real.exp (T + Δ - C) ≤ R) (hgap : Real.log 2 + 2 * C < Δ - E) :
    2 * K * B < R := by
  have h : (2 : ℝ) * K * B < R := by
    calc
      _ ≤ 2 * Real.exp (T + C) * Real.exp E := by gcongr
      _ = Real.exp (Real.log 2 + (T + C) + E) := by
        simp only [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ < Real.exp (T + Δ - C) := Real.exp_lt_exp.mpr (by linarith)
      _ ≤ R := hR
  exact_mod_cast h

/-- Rounding the new exponential frequency cutoff downward costs at most
one factor two, which is covered by the same square-root reserve. -/
theorem transfer_integer_frequency_cutoff (M H B V : ℕ) (T Δ E E' C : ℝ)
    (hM : Real.exp (T - C) ≤ M) (hH : (H : ℝ) ≤ Real.exp (T + Δ + C))
    (hB : (B : ℝ) ≤ Real.exp E) (hV : Real.exp E' ≤ 2 * V)
    (hgap : Real.log 4 + 2 * C + E + Δ ≤ E') :
    2 * B * H ≤ V * M := by
  have hhalf : Real.exp E' / 2 ≤ (V : ℝ) := by linarith
  have h : (2 : ℝ) * B * H ≤ V * M := by
    calc
      _ ≤ 2 * Real.exp E * Real.exp (T + Δ + C) := by gcongr
      _ = Real.exp (Real.log 2 + E + (T + Δ + C)) := by
        simp only [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ Real.exp (E' - Real.log 2 + (T - C)) := Real.exp_le_exp.mpr (by
        have hlog : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          norm_num
        rw [hlog] at hgap
        linarith)
      _ = (Real.exp E' / 2) * Real.exp (T - C) := by
        rw [Real.exp_add, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ V * M := mul_le_mul hhalf hM (Real.exp_pos _).le (Nat.cast_nonneg _)
  exact_mod_cast h

end Ostmann

end OAI
