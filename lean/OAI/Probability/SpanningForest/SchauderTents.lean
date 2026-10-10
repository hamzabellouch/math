import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.SchauderTents

def unitTent (t : ℝ) : ℝ := max 0 (min t (1 - t))

theorem continuous_unitTent : Continuous unitTent := by
  unfold unitTent
  fun_prop

theorem unitTent_nonneg (t : ℝ) : 0 ≤ unitTent t := le_max_left _ _

theorem unitTent_le_half (t : ℝ) : unitTent t ≤ 1 / 2 := by
  unfold unitTent
  apply max_le (by norm_num)
  by_cases h : t ≤ 1 / 2
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

theorem unitTent_pos_iff (t : ℝ) : 0 < unitTent t ↔ 0 < t ∧ t < 1 := by
  simp only [unitTent, lt_max_iff, lt_self_iff_false, false_or, lt_min_iff]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem unitTent_ne_zero_iff (t : ℝ) : unitTent t ≠ 0 ↔ 0 < t ∧ t < 1 := by
  constructor
  · intro h
    exact (unitTent_pos_iff t).mp (lt_of_le_of_ne (unitTent_nonneg t) h.symm)
  · intro h
    exact ne_of_gt ((unitTent_pos_iff t).mpr h)

theorem unitTent_eq_zero_of_le_zero {t : ℝ} (ht : t ≤ 0) : unitTent t = 0 := by
  apply le_antisymm _ (unitTent_nonneg t)
  exact max_le le_rfl ((min_le_left _ _).trans ht)

theorem unitTent_eq_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) : unitTent t = 0 := by
  apply le_antisymm _ (unitTent_nonneg t)
  exact max_le le_rfl ((min_le_right _ _).trans (by linarith))

@[simp] theorem unitTent_half : unitTent (1 / 2) = 1 / 2 := by
  norm_num [unitTent]

theorem unitTent_of_left {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1 / 2) :
    unitTent t = t := by
  unfold unitTent
  rw [min_eq_left (by linarith), max_eq_right h₀]

theorem unitTent_of_right {t : ℝ} (h₀ : 1 / 2 ≤ t) (h₁ : t ≤ 1) :
    unitTent t = 1 - t := by
  unfold unitTent
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

theorem unitTent_midpoint_of_no_corner {a b : ℝ} (hab : a ≤ b)
    (h : b ≤ 0 ∨ (0 ≤ a ∧ b ≤ 1 / 2) ∨ (1 / 2 ≤ a ∧ b ≤ 1) ∨ 1 ≤ a) :
    unitTent ((a + b) / 2) = (unitTent a + unitTent b) / 2 := by
  rcases h with h | h | h | h
  · rw [unitTent_eq_zero_of_le_zero (by linarith),
      unitTent_eq_zero_of_le_zero (by linarith), unitTent_eq_zero_of_le_zero h]
    norm_num
  · rw [unitTent_of_left (by linarith [h.1]) (by linarith [h.2]),
      unitTent_of_left h.1 (by linarith [h.2]),
      unitTent_of_left (by linarith [h.1]) h.2]
  · rw [unitTent_of_right (by linarith [h.1]) (by linarith [h.2]),
      unitTent_of_right h.1 (by linarith [h.2]),
      unitTent_of_right (by linarith [h.1]) h.2]
    ring
  · rw [unitTent_eq_zero_of_one_le (by linarith), unitTent_eq_zero_of_one_le h,
      unitTent_eq_zero_of_one_le (by linarith)]
    norm_num

theorem unitTent_even_grid_midpoint (d j k : ℕ) (hd : 0 < d) :
    unitTent (((j : ℝ) + 1 / 2) / (2 * d) - k) =
      (unitTent ((j : ℝ) / (2 * d) - k) +
        unitTent (((j : ℝ) + 1) / (2 * d) - k)) / 2 := by
  have hden : 0 < (2 : ℝ) * d := by positivity
  have hden_ne : (2 : ℝ) * d ≠ 0 := ne_of_gt hden
  have hmid : ((j : ℝ) + 1 / 2) / (2 * d) - k =
      (((j : ℝ) / (2 * d) - k) + (((j : ℝ) + 1) / (2 * d) - k)) / 2 := by
    ring
  rw [hmid]
  apply unitTent_midpoint_of_no_corner
  · exact sub_le_sub_right (div_le_div_of_nonneg_right (by linarith) hden.le) _
  · by_cases h₀ : j < 2 * d * k
    · left
      have hj : (j : ℝ) + 1 ≤ 2 * d * k := by exact_mod_cast (Nat.succ_le_of_lt h₀)
      exact sub_nonpos.mpr ((div_le_iff₀ hden).mpr (by nlinarith))
    · have h₀' : 2 * d * k ≤ j := le_of_not_gt h₀
      have ha : 0 ≤ (j : ℝ) / (2 * d) - k := by
        apply sub_nonneg.mpr
        apply (le_div_iff₀ hden).mpr
        have : (2 : ℝ) * d * k ≤ j := by exact_mod_cast h₀'
        nlinarith
      by_cases h₁ : j < 2 * d * k + d
      · right; left
        refine ⟨ha, ?_⟩
        apply sub_le_iff_le_add.mpr
        apply (div_le_iff₀ hden).mpr
        have : (j : ℝ) + 1 ≤ 2 * d * k + d := by exact_mod_cast (Nat.succ_le_of_lt h₁)
        nlinarith
      · have h₁' : 2 * d * k + d ≤ j := le_of_not_gt h₁
        have ha' : 1 / 2 ≤ (j : ℝ) / (2 * d) - k := by
          apply le_sub_iff_add_le.mpr
          apply (le_div_iff₀ hden).mpr
          have : (2 : ℝ) * d * k + d ≤ j := by exact_mod_cast h₁'
          nlinarith
        by_cases h₂ : j < 2 * d * (k + 1)
        · right; right; left
          refine ⟨ha', ?_⟩
          apply sub_le_iff_le_add.mpr
          apply (div_le_iff₀ hden).mpr
          have : (j : ℝ) + 1 ≤ 2 * d * (k + 1) := by exact_mod_cast (Nat.succ_le_of_lt h₂)
          nlinarith
        · right; right; right
          apply le_sub_iff_add_le.mpr
          apply (le_div_iff₀ hden).mpr
          have : (2 : ℝ) * d * (k + 1) ≤ j := by exact_mod_cast (le_of_not_gt h₂)
          nlinarith

def amplitude (n : ℕ) : ℝ := (Real.sqrt 2)⁻¹ ^ n

theorem amplitude_pos (n : ℕ) : 0 < amplitude n := by
  unfold amplitude
  positivity

def tent (n k : ℕ) (t : ℝ) : ℝ :=
  amplitude n * unitTent ((2 : ℝ) ^ n * t - k)

theorem continuous_tent (n k : ℕ) : Continuous (tent n k) := by
  exact continuous_const.mul (continuous_unitTent.comp (by fun_prop))

theorem tent_nonneg (n k : ℕ) (t : ℝ) : 0 ≤ tent n k t :=
  mul_nonneg (amplitude_pos n).le (unitTent_nonneg _)

theorem tent_le_half_amplitude (n k : ℕ) (t : ℝ) :
    tent n k t ≤ amplitude n / 2 := by
  unfold tent
  simpa only [mul_one_div] using
    mul_le_mul_of_nonneg_left (unitTent_le_half ((2 : ℝ) ^ n * t - k))
      (amplitude_pos n).le

theorem tent_ne_zero_iff (n k : ℕ) (t : ℝ) :
    tent n k t ≠ 0 ↔ (k : ℝ) < 2 ^ n * t ∧ 2 ^ n * t < k + 1 := by
  rw [tent, mul_ne_zero_iff, and_iff_right (ne_of_gt (amplitude_pos n)),
    unitTent_ne_zero_iff]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem tent_disjoint (n : ℕ) {k l : ℕ} (hkl : k ≠ l) (t : ℝ)
    (hk : tent n k t ≠ 0) : tent n l t = 0 := by
  by_contra hl
  obtain ⟨hk₁, hk₂⟩ := (tent_ne_zero_iff n k t).mp hk
  obtain ⟨hl₁, hl₂⟩ := (tent_ne_zero_iff n l t).mp hl
  rcases lt_or_gt_of_ne hkl with h | h
  · have : (k : ℝ) + 1 ≤ l := by exact_mod_cast h
    linarith
  · have : (l : ℝ) + 1 ≤ k := by exact_mod_cast h
    linarith

def level (n : ℕ) (z : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), z k * tent n k t

theorem continuous_level (n : ℕ) (z : ℕ → ℝ) : Continuous (level n z) := by
  unfold level
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_tent n k)

theorem abs_level_le (n : ℕ) (z : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hz : ∀ k < 2 ^ n, |z k| ≤ C) (t : ℝ) :
    |level n z t| ≤ C * amplitude n / 2 := by
  classical
  by_cases h : ∃ k ∈ Finset.range (2 ^ n), tent n k t ≠ 0
  · obtain ⟨k, hk, hkt⟩ := h
    have hsum : level n z t = z k * tent n k t := by
      unfold level
      apply Finset.sum_eq_single k
      · intro l hl hlk
        rw [tent_disjoint n (Ne.symm hlk) t hkt, mul_zero]
      · exact fun hnot => (hnot hk).elim
    rw [hsum, abs_mul, abs_of_nonneg (tent_nonneg n k t)]
    calc
      |z k| * tent n k t ≤ C * tent n k t :=
        mul_le_mul_of_nonneg_right (hz k (Finset.mem_range.mp hk)) (tent_nonneg n k t)
      _ ≤ C * (amplitude n / 2) :=
        mul_le_mul_of_nonneg_left (tent_le_half_amplitude n k t) hC
      _ = C * amplitude n / 2 := by ring
  · have hzero : level n z t = 0 := by
      unfold level
      apply Finset.sum_eq_zero
      intro k hk
      have hkt : tent n k t = 0 := by
        by_contra hne
        exact h ⟨k, hk, hne⟩
      rw [hkt, mul_zero]
    rw [hzero, abs_zero]
    exact div_nonneg (mul_nonneg hC (amplitude_pos n).le) (by norm_num)

theorem unitTent_nat_sub (j k : ℕ) : unitTent ((j : ℝ) - k) = 0 := by
  by_cases h : j ≤ k
  · apply unitTent_eq_zero_of_le_zero
    have : (j : ℝ) ≤ k := by exact_mod_cast h
    linarith
  · apply unitTent_eq_zero_of_one_le
    have : (k : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt (lt_of_not_ge h))
    linarith

theorem tent_grid_zero (n k j : ℕ) : tent n k ((j : ℝ) / 2 ^ n) = 0 := by
  have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have harg : (2 : ℝ) ^ n * ((j : ℝ) / 2 ^ n) - k = (j : ℝ) - k := by
    field_simp
  rw [tent, harg, unitTent_nat_sub, mul_zero]

theorem tent_prior_grid_zero (n r k j : ℕ) :
    tent (n + r) k ((j : ℝ) / 2 ^ n) = 0 := by
  have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have harg : (2 : ℝ) ^ (n + r) * ((j : ℝ) / 2 ^ n) - k =
      (((2 ^ r * j : ℕ) : ℝ) - k) := by
    push_cast
    rw [pow_add]
    field_simp
  rw [tent, harg, unitTent_nat_sub, mul_zero]

theorem level_prior_grid_zero (n r j : ℕ) (z : ℕ → ℝ) :
    level (n + r) z ((j : ℝ) / 2 ^ n) = 0 := by
  simp [level, tent_prior_grid_zero]

def midpoint (n k : ℕ) : ℝ := ((k : ℝ) + 1 / 2) / 2 ^ n

theorem tent_at_midpoint (n k : ℕ) :
    tent n k (midpoint n k) = amplitude n / 2 := by
  have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have harg : (2 : ℝ) ^ n * midpoint n k - k = 1 / 2 := by
    unfold midpoint
    field_simp
    ring
  rw [tent, harg, unitTent_half]
  ring

theorem tent_at_other_midpoint (n : ℕ) {k l : ℕ} (hkl : k ≠ l) :
    tent n l (midpoint n k) = 0 := by
  apply tent_disjoint n hkl
  rw [tent_at_midpoint]
  exact ne_of_gt (div_pos (amplitude_pos n) (by norm_num))

theorem level_at_midpoint (n k : ℕ) (z : ℕ → ℝ) (hk : k < 2 ^ n) :
    level n z (midpoint n k) = z k * amplitude n / 2 := by
  classical
  unfold level
  rw [Finset.sum_eq_single k]
  · rw [tent_at_midpoint]
    ring
  · intro l hl hlk
    rw [tent_at_other_midpoint n (Ne.symm hlk), mul_zero]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hk)).elim

theorem tent_old_midpoint (m r k j : ℕ) :
    tent m k (midpoint (m + r + 1) j) =
      (tent m k ((j : ℝ) / 2 ^ (m + r + 1)) +
        tent m k (((j : ℝ) + 1) / 2 ^ (m + r + 1))) / 2 := by
  have hscale (q : ℝ) :
      (2 : ℝ) ^ m * (q / 2 ^ (m + r + 1)) = q / (2 * (2 ^ r : ℕ)) := by
    push_cast
    rw [pow_add, pow_add, pow_one]
    field_simp
  simp only [tent, midpoint, hscale]
  rw [unitTent_even_grid_midpoint (2 ^ r) j k (by positivity)]
  ring

theorem tent_old_midpoint_of_lt {m n : ℕ} (hmn : m < n) (k j : ℕ) :
    tent m k (midpoint n j) =
      (tent m k ((j : ℝ) / 2 ^ n) + tent m k (((j : ℝ) + 1) / 2 ^ n)) / 2 := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hmn)
  have hn : n = m + r + 1 := by omega
  rw [hn]
  exact tent_old_midpoint m r k j

theorem level_old_midpoint {m n : ℕ} (hmn : m < n) (z : ℕ → ℝ) (j : ℕ) :
    level m z (midpoint n j) =
      (level m z ((j : ℝ) / 2 ^ n) + level m z (((j : ℝ) + 1) / 2 ^ n)) / 2 := by
  simp only [level, tent_old_midpoint_of_lt hmn, ← mul_div_assoc, mul_add,
    ← Finset.sum_div, Finset.sum_add_distrib]

end Problem336.SchauderTents

end

end OAI
