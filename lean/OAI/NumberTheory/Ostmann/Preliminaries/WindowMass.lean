import OAI.NumberTheory.Ostmann.Preliminaries.UpperWindow

namespace OAI

open Erdos970

namespace Ostmann.Preliminaries
open Filter
open scoped BigOperators

theorem eventually_upperWindow_card_lower (S : Set ℕ) {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ᶠ X : ℕ in atTop,
      c * Real.sqrt X / Real.log (X : ℝ) ^ 3 ≤ countUpTo S X)
    (hupper : ∀ᶠ X : ℕ in atTop,
      (countUpTo S X : ℝ) ≤ C * Real.sqrt X * Real.log (X : ℝ) ^ 2) :
    ∀ᶠ X : ℕ in atTop,
      (c / 2) * Real.sqrt X / Real.log (X : ℝ) ^ 3 ≤ (upperWindow S X).card := by
  filter_upwards [hlower, initialWindowCutoff_tendsto.eventually hupper,
    eventually_initial_window_scale hc hC, initialWindowCutoff_tendsto.eventually_ge_atTop 2,
    eventually_ge_atTop 2] with X hlower hupper hsmall hcut hX
  have hxr : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hcutr : (1 : ℝ) ≤ initialWindowCutoff X := by exact_mod_cast (show 1 ≤ initialWindowCutoff X by omega)
  have hfloor : (initialWindowCutoff X : ℝ) ≤ (X : ℝ) ^ (9 / 10 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  have hpowX : (X : ℝ) ^ (9 / 10 : ℝ) ≤ X :=
    Real.rpow_le_self_of_one_le hxr (by norm_num)
  have hlogs : Real.log (initialWindowCutoff X : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by linarith) (hfloor.trans hpowX)
  have hsqrt : Real.sqrt (initialWindowCutoff X : ℝ) ≤ (X : ℝ) ^ (9 / 20 : ℝ) := by
    have hid : Real.sqrt ((X : ℝ) ^ (9 / 10 : ℝ)) = (X : ℝ) ^ (9 / 20 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (show (0 : ℝ) ≤ X by positivity)]
      norm_num
    simpa only [hid] using Real.sqrt_le_sqrt hfloor
  have hcountsmall : (countUpTo S (initialWindowCutoff X) : ℝ) ≤
      (c / 2) * Real.sqrt X / Real.log (X : ℝ) ^ 3 := by
    apply le_trans (hupper.trans ?_) hsmall
    gcongr
  have htotal : (countUpTo S X : ℝ) ≤
      (upperWindow S X).card + countUpTo S (initialWindowCutoff X) := by
    exact_mod_cast countUpTo_le_upperWindow_add_initial S X
  have hid : (c / 2) * Real.sqrt X / Real.log (X : ℝ) ^ 3 +
      (c / 2) * Real.sqrt X / Real.log (X : ℝ) ^ 3 =
      c * Real.sqrt X / Real.log (X : ℝ) ^ 3 := by ring
  linarith

noncomputable def uniformWindowMass (S : Set ℕ) (X : ℕ) (_ : upperWindow S X) : ℝ :=
  ((upperWindow S X).card : ℝ)⁻¹

theorem uniformWindowMass_nonneg (S : Set ℕ) (X : ℕ) (i : upperWindow S X) :
    0 ≤ uniformWindowMass S X i := by unfold uniformWindowMass; positivity

theorem uniformWindowMass_sum (S : Set ℕ) (X : ℕ) (h : (upperWindow S X).Nonempty) :
    ∑ i : upperWindow S X, uniformWindowMass S X i = 1 := by
  have hc : ((upperWindow S X).card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt h.card_pos
  simp [uniformWindowMass, hc]

theorem eventually_uniformWindowMass_cap (S : Set ℕ) {c : ℝ} (hc : 0 < c)
    (hcard : ∀ᶠ X : ℕ in atTop,
      c * Real.sqrt X / Real.log (X : ℝ) ^ 3 ≤ (upperWindow S X).card) :
    ∀ᶠ X : ℕ in atTop, (upperWindow S X).Nonempty ∧
      ∀ i : upperWindow S X, uniformWindowMass S X i ≤ collisionMassCap 4 X := by
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop c⁻¹
  filter_upwards [hcard, hlog, eventually_ge_atTop 2] with X hcard hlog hX
  change c⁻¹ ≤ Real.log (X : ℝ) at hlog
  have hxr : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hsqrt : 0 < Real.sqrt X := Real.sqrt_pos.mpr hxr
  have hl : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hcardpos : (0 : ℝ) < (upperWindow S X).card :=
    (div_pos (mul_pos hc hsqrt) (pow_pos hl 3)).trans_le hcard
  have hcardnat : 0 < (upperWindow S X).card := by exact_mod_cast hcardpos
  refine ⟨Finset.card_pos.mp hcardnat, fun i => ?_⟩
  have hnum := (div_le_iff₀ (pow_pos hl 3)).mp hcard
  have hscale : 1 ≤ c * Real.log (X : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlog hc.le
    simpa only [mul_inv_cancel₀ (ne_of_gt hc)] using h
  have hmul := mul_le_mul_of_nonneg_right hnum hl.le
  have hscale2 := mul_le_mul_of_nonneg_right hscale hsqrt.le
  unfold uniformWindowMass collisionMassCap
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ hcardpos hsqrt).mpr
  nlinarith [hmul, hscale2]

end Ostmann.Preliminaries

end OAI
