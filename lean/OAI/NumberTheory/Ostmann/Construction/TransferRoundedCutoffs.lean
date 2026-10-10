import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Rat.Floor
import OAI.NumberTheory.Ostmann.Construction.TransferGapRanges

namespace OAI

/-! # Natural cutoffs supplied by the transfer's exponential ranges -/

namespace Ostmann

open Filter
open scoped Topology

noncomputable def naturalTransferCutoff (Δ m : ℝ) (j : ℕ) : ℕ :=
  ⌊Real.exp (transferErrorScale Δ m j)⌋₊

noncomputable def naturalProductCap (T : ℝ) : ℕ := ⌊Real.exp T⌋₊

theorem natural_exp_cutoff_bounds (E : ℝ) (hE : Real.log 2 ≤ E) :
    0 < ⌊Real.exp E⌋₊ ∧ (⌊Real.exp E⌋₊ : ℝ) ≤ Real.exp E ∧
      Real.exp E ≤ 2 * (⌊Real.exp E⌋₊ : ℝ) := by
  have hexp : (2 : ℝ) ≤ Real.exp E := by
    calc
      _ = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp E := Real.exp_le_exp.mpr hE
  have hn : 1 ≤ ⌊Real.exp E⌋₊ := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hnR : (1 : ℝ) ≤ ⌊Real.exp E⌋₊ := by exact_mod_cast hn
  exact ⟨hn, Nat.floor_le (Real.exp_pos _).le, by linarith [Nat.lt_floor_add_one (Real.exp E)]⟩

/-- The same explicit rounded cutoffs supply the strict determinant gap
and the next signed-frequency bound, at every transfer level. -/
theorem eventually_transfer_integer_ranges (C : ℝ) :
    ∀ᶠ m : ℝ in atTop, ∀ Δ : ℝ, 0 ≤ Δ → ∀ j : ℕ, ∀ T : ℝ,
      ∀ M R : ℕ,
      Real.exp (T - C) ≤ M → Real.exp (T + transferNextGap Δ m j - C) ≤ R →
      2 * naturalProductCap (T + C) * naturalTransferCutoff Δ m j < R ∧
      2 * naturalTransferCutoff Δ m j * naturalProductCap (T + transferNextGap Δ m j + C) ≤
        naturalTransferCutoff Δ m (j + 1) * M := by
  filter_upwards [eventually_transfer_reserve C,
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (Real.log 2 / 2))] with m hm hsqrt
  intro Δ hΔ j T M R hM hR
  obtain ⟨hgap, hnext⟩ := hm Δ j
  have hlog : Real.log (2 : ℝ) ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have hfloor (x : ℝ) : (naturalProductCap x : ℝ) ≤ Real.exp x :=
    Nat.floor_le (Real.exp_pos _).le
  have hB : (naturalTransferCutoff Δ m j : ℝ) ≤ Real.exp (transferErrorScale Δ m j) :=
    Nat.floor_le (Real.exp_pos _).le
  have hE : Real.log 2 ≤ transferErrorScale Δ m (j + 1) := by
    have hp : 1 ≤ (4 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
    have hD : 0 ≤ (2 : ℝ) ^ (j + 1) * Δ := mul_nonneg (by positivity) hΔ
    have hs0 := Real.sqrt_nonneg m
    unfold transferErrorScale
    nlinarith
  have hV := (natural_exp_cutoff_bounds (transferErrorScale Δ m (j + 1)) hE).2.2
  constructor
  · exact transfer_integer_rigidity_gap _ _ R T (transferNextGap Δ m j)
      (transferErrorScale Δ m j) C (hfloor _) hB hR (by linarith)
  · exact transfer_integer_frequency_cutoff M _ _ _ T (transferNextGap Δ m j)
      (transferErrorScale Δ m j) (transferErrorScale Δ m (j + 1)) C hM (hfloor _) hB hV
      (by linarith)

end Ostmann

end OAI
