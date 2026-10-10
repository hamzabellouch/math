import OAI.NumberTheory.Ostmann.Preliminaries.CollisionBound
import OAI.NumberTheory.Ostmann.Preliminaries.SquareRootTransfer

namespace OAI

open Erdos970

namespace Ostmann.Preliminaries
open Filter
open scoped BigOperators

noncomputable def upperWindow (A : Set ℕ) (X : ℕ) : Finset ℕ := by
  classical
  exact (elementsUpTo A X).filter (fun a => (X : ℝ) ^ (9 / 10 : ℝ) ≤ a)

noncomputable def initialWindowCutoff (X : ℕ) : ℕ := ⌊(X : ℝ) ^ (9 / 10 : ℝ)⌋₊

@[simp] theorem mem_upperWindow {A : Set ℕ} {X a : ℕ} :
    a ∈ upperWindow A X ↔ a ∈ A ∧ a ≤ X ∧ (X : ℝ) ^ (9 / 10 : ℝ) ≤ a := by
  classical
  simp only [upperWindow, Finset.mem_filter, mem_elementsUpTo, and_assoc]

theorem countUpTo_le_upperWindow_add_initial (A : Set ℕ) (X : ℕ) :
    countUpTo A X ≤ (upperWindow A X).card + countUpTo A (initialWindowCutoff X) := by
  classical
  have hsub : elementsUpTo A X ⊆ upperWindow A X ∪ elementsUpTo A (initialWindowCutoff X) := by
    intro a ha
    obtain ⟨hA, hX⟩ := mem_elementsUpTo.mp ha
    by_cases hlarge : (X : ℝ) ^ (9 / 10 : ℝ) ≤ a
    · exact Finset.mem_union.mpr (Or.inl (mem_upperWindow.mpr ⟨hA, hX, hlarge⟩))
    · exact Finset.mem_union.mpr (Or.inr (mem_elementsUpTo.mpr
        ⟨hA, Nat.le_floor (le_of_lt (lt_of_not_ge hlarge))⟩))
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem initialWindowCutoff_tendsto : Tendsto initialWindowCutoff atTop atTop := by
  have hpow := (tendsto_rpow_atTop (show (0 : ℝ) < 9 / 10 by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_atTop.2
  intro n
  filter_upwards [hpow.eventually_ge_atTop (n : ℝ)] with X hX
  exact Nat.le_floor hX

theorem eventually_upperWindow_large (N : ℕ) :
    ∀ᶠ X : ℕ in atTop, Real.sqrt X + N < (X : ℝ) ^ (9 / 10 : ℝ) := by
  have hnat : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow := (tendsto_rpow_atTop (show (0 : ℝ) < 2 / 5 by norm_num)).comp hnat
  have hroot := Real.tendsto_sqrt_atTop.comp hnat
  filter_upwards [hpow.eventually_ge_atTop 2, hroot.eventually_gt_atTop (N : ℝ),
    eventually_ge_atTop 1] with X hp hr hX
  have hxr : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hid : Real.sqrt X * (X : ℝ) ^ (2 / 5 : ℝ) = (X : ℝ) ^ (9 / 10 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hxr]
    norm_num
  change 2 ≤ (X : ℝ) ^ (2 / 5 : ℝ) at hp
  change (N : ℝ) < Real.sqrt X at hr
  have hmul := mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg (X : ℝ))
  rw [hid] at hmul
  nlinarith

theorem eventually_initial_window_scale {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∀ᶠ X : ℕ in atTop,
      C * (X : ℝ) ^ (9 / 20 : ℝ) * Real.log (X : ℝ) ^ 2 ≤
        (c / 2) * Real.sqrt X / Real.log (X : ℝ) ^ 3 := by
  have he : 0 < c / (2 * C) := by positivity
  have hsmall := (isLittleO_log_rpow_rpow_atTop (5 : ℝ)
    (show (0 : ℝ) < 1 / 20 by norm_num)).bound he
  have hnat : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually hsmall, eventually_ge_atTop 2] with X hsmall hX
  have hxr : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hl : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  norm_num only [Real.rpow_ofNat] at hsmall
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hl.le 5),
    abs_of_nonneg (Real.rpow_nonneg hxr.le _)] at hsmall
  have hmul := mul_le_mul_of_nonneg_left hsmall
    (show 0 ≤ C * (X : ℝ) ^ (9 / 20 : ℝ) by positivity)
  have hid : (X : ℝ) ^ (9 / 20 : ℝ) * (X : ℝ) ^ (1 / 20 : ℝ) = Real.sqrt X := by
    rw [← Real.rpow_add hxr, Real.sqrt_eq_rpow]
    norm_num
  have hright : (C * (X : ℝ) ^ (9 / 20 : ℝ)) *
      ((c / (2 * C)) * (X : ℝ) ^ (1 / 20 : ℝ)) = (c / 2) * Real.sqrt X := by
    rw [← hid]
    field_simp
  apply (le_div_iff₀ (pow_pos hl 3)).mpr
  rw [hright] at hmul
  nlinarith

end Ostmann.Preliminaries

end OAI
