import Mathlib.Analysis.SpecialFunctions.Log.Basic
import OAI.NumberTheory.Ostmann.Construction.OriginalAveragedTransfer

namespace OAI

/-! # The actual factorial and harmonic-mass loss in the transfer iteration -/

namespace Ostmann

open scoped BigOperators Classical
open Filter

noncomputable def pivotLogLoss (n : ℕ) (C L : ℝ) : ℝ :=
  Real.log (n.factorial : ℝ) + (n : ℝ) * C * L

theorem pivotLogLoss_nonneg (n : ℕ) (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) :
    0 ≤ pivotLogLoss n C L := by
  have hn : (1 : ℝ) ≤ n.factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
  exact add_nonneg (Real.log_nonneg hn) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) hL)

theorem harmonic_pivot_loss_le {n : ℕ} (Q : Fin n → Finset ℕ) (C L : ℝ)
    (hmass : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (C * L)) :
    ((n.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) ≤
      Real.exp (pivotLogLoss n C L) := by
  have hprod : (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) ≤ Real.exp ((n : ℝ) * C * L) := by
    calc
      _ ≤ ∏ _i : Fin n, Real.exp (C * L) :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => hmass i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← Real.exp_nat_mul]; congr 1; ring
  calc
    _ ≤ (n.factorial : ℝ) * Real.exp ((n : ℝ) * C * L) :=
      mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
    _ = _ := by
      rw [pivotLogLoss, Real.exp_add, Real.exp_log (by exact_mod_cast Nat.factorial_pos n)]

/-- For fixed depth the factorial terms are constants in L. The selected
cell-role budget leaves enough room for all Cauchy losses and floor rounding. -/
theorem eventual_pivot_loss_budget (k : ℕ) (r : Fin k → ℕ) (C z : ℝ)
    (hC : 0 ≤ C) (hz : 0 < z) (hsmall : C * (∑ j, (r j : ℝ)) ≤ z / 4) :
    ∀ᶠ L : ℝ in atTop,
      (∀ j, 0 ≤ pivotLogLoss (r j) C L) ∧
      (∑ j, (pivotLogLoss (r j) C L + Real.log 2)) ≤ (⌊z * L⌋₊ : ℝ) := by
  let F := ∑ j, (Real.log ((r j).factorial : ℝ) + Real.log 2)
  filter_upwards [eventually_ge_atTop (max 0 (max (4 * F / z) (2 / z)))] with L hL
  have hL0 : 0 ≤ L := (le_max_left _ _).trans hL
  have hF : 4 * F / z ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have htwo : 2 / z ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hFL : F ≤ z * L / 4 := by
    have hh := (div_le_iff₀ hz).mp hF
    nlinarith
  have hzL : 2 ≤ z * L := by
    have hh := (div_le_iff₀ hz).mp htwo
    nlinarith
  refine ⟨fun j => pivotLogLoss_nonneg (r j) C L hC hL0, ?_⟩
  have hs : (∑ j, (pivotLogLoss (r j) C L + Real.log 2)) =
      C * (∑ j, (r j : ℝ)) * L + F := by
    dsimp [pivotLogLoss, F]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  rw [hs]
  have hc := mul_le_mul_of_nonneg_right hsmall hL0
  have hfloor := Nat.lt_floor_add_one (z * L)
  nlinarith

end Ostmann

end OAI
