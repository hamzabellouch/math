import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorExpectation
import Mathlib.Data.Nat.Choose.Bounds

namespace OAI

/-! # Finite rounded family sizes and expected incidence bounds -/

noncomputable section

namespace LowSpaceSubsetSum.SeparatorExpectation

/-- Rounding the sampled family size costs at most one extra trial. -/
theorem rounded_family_mass {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (⌈10 / θ⌉₊ : ℝ) * θ ≤ 11 := by
  have h := (Nat.ceil_lt_add_one (show 0 ≤ 10 / θ by positivity)).le
  have hm := mul_le_mul_of_nonneg_right h hθ.le
  rw [add_mul, div_mul_cancel₀ _ hθ.ne', one_mul] at hm
  linarith

theorem rounded_family_incidence (A D N : ℕ) (hD : 0 < D) (hN : 0 < N)
    (hDN : D ≤ N) :
    (⌈10 / ((D : ℝ) / N)⌉₊ : ℝ) * ((A : ℝ) / N) ≤ 11 * ((A : ℝ) / D) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hθ1 : (D : ℝ) / N ≤ 1 := (div_le_one hNR).mpr (by exact_mod_cast hDN)
  have hm := rounded_family_mass (div_pos hDR hNR) hθ1
  have he : (⌈10 / ((D : ℝ) / N)⌉₊ : ℝ) * ((A : ℝ) / N) =
      ((⌈10 / ((D : ℝ) / N)⌉₊ : ℝ) * ((D : ℝ) / N)) * ((A : ℝ) / D) := by
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_right hm (by positivity)

/-- This bound is uniform over every admissible sampled family. -/
theorem rounded_family_size (g e c : ℕ) (he : e ≤ g) (hfeas : e - c ≤ g / 2)
    (hDN : (g / 2).choose (e - c) ≤ g.choose e) :
    ⌈10 / ((Nat.choose (g / 2) (e - c) : ℝ) / Nat.choose g e)⌉₊ ≤ 11 * 2 ^ g := by
  have hD : 0 < (g / 2).choose (e - c) := Nat.choose_pos hfeas
  have hN : 0 < g.choose e := Nat.choose_pos he
  have hm := rounded_family_incidence (g.choose e) ((g / 2).choose (e - c))
    (g.choose e) hD hN hDN
  have hNR : (0 : ℝ) < g.choose e := by exact_mod_cast hN
  rw [div_self hNR.ne', mul_one] at hm
  have hr : (g.choose e : ℝ) / (g / 2).choose (e - c) ≤ g.choose e := by
    apply div_le_self (by positivity)
    exact_mod_cast hD
  have hb : (⌈10 / ((Nat.choose (g / 2) (e - c) : ℝ) / Nat.choose g e)⌉₊ : ℝ) ≤
      11 * (2 : ℝ) ^ g := by
    calc
      _ ≤ 11 * ((g.choose e : ℝ) / (g / 2).choose (e - c)) := hm
      _ ≤ 11 * (g.choose e : ℝ) := mul_le_mul_of_nonneg_left hr (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.choose_le_two_pow g e) (by norm_num)
  exact_mod_cast hb

theorem rounded_family_depth (g e c : ℕ) (he : e ≤ g) (hfeas : e - c ≤ g / 2)
    (hDN : (g / 2).choose (e - c) ≤ g.choose e) :
    Nat.clog 2 (⌈10 / ((Nat.choose (g / 2) (e - c) : ℝ) / Nat.choose g e)⌉₊) ≤ g + 4 := by
  apply Nat.clog_le_of_le_pow
  have h := rounded_family_size g e c he hfeas hDN
  calc
    _ ≤ 11 * 2 ^ g := h
    _ ≤ 2 ^ (g + 4) := by rw [pow_add]; norm_num; omega

end LowSpaceSubsetSum.SeparatorExpectation

end

end OAI
