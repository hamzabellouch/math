import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace OAI

noncomputable section

namespace ThompsonNonamenability.Analytic

open scoped NNReal

def a (t : ℝ) : ℝ :=
  if t ≤ 2 then t / 8 else if t < 3 then 5 / 16 - (3 - t) ^ 2 / 16 else 5 / 16

/-- The derivative profile of `a`, with its common values at the junctions. -/
def aDeriv (t : ℝ) : ℝ :=
  if t ≤ 2 then 1 / 8 else if t < 3 then (3 - t) / 8 else 0

def theta (t : ℝ) : ℝ :=
  if t ≤ 1 then 0 else if t < 2 then (t - 1) ^ 2 / 2 else t - 3 / 2

/-- The derivative profile of `theta`. -/
def thetaDeriv (t : ℝ) : ℝ :=
  if t ≤ 1 then 0 else if t < 2 then t - 1 else 1

/-- The radial coefficient of the modified curve. -/
def b (t : ℝ) : ℝ := min (a t) (-(1 / 8))

/-- The bounded radial correction used in the tube. -/
def q (t : ℝ) : ℝ := -max (a t + 1 / 8) 0

theorem a_of_le_two {t : ℝ} (h : t ≤ 2) : a t = t / 8 := by simp [a, h]

theorem a_of_two_lt_of_lt_three {t : ℝ} (h : 2 < t) (h' : t < 3) :
    a t = 5 / 16 - (3 - t) ^ 2 / 16 := by simp [a, not_le.mpr h, h']

theorem a_of_three_le {t : ℝ} (h : 3 ≤ t) : a t = 5 / 16 := by
  simp [a, show ¬t ≤ 2 by linarith, not_lt.mpr h]

theorem aDeriv_of_le_two {t : ℝ} (h : t ≤ 2) : aDeriv t = 1 / 8 := by
  simp [aDeriv, h]

theorem aDeriv_of_three_le {t : ℝ} (h : 3 ≤ t) : aDeriv t = 0 := by
  simp [aDeriv, show ¬t ≤ 2 by linarith, not_lt.mpr h]

theorem theta_of_le_one {t : ℝ} (h : t ≤ 1) : theta t = 0 := by simp [theta, h]

theorem theta_of_one_lt_of_lt_two {t : ℝ} (h : 1 < t) (h' : t < 2) :
    theta t = (t - 1) ^ 2 / 2 := by simp [theta, not_le.mpr h, h']

theorem theta_of_two_le {t : ℝ} (h : 2 ≤ t) : theta t = t - 3 / 2 := by
  simp [theta, show ¬t ≤ 1 by linarith, not_lt.mpr h]

theorem thetaDeriv_of_le_one {t : ℝ} (h : t ≤ 1) : thetaDeriv t = 0 := by
  simp [thetaDeriv, h]

theorem thetaDeriv_of_two_le {t : ℝ} (h : 2 ≤ t) : thetaDeriv t = 1 := by
  simp [thetaDeriv, show ¬t ≤ 1 by linarith, not_lt.mpr h]

theorem a_le_five_sixteenths (t : ℝ) : a t ≤ 5 / 16 := by
  unfold a
  split_ifs <;> nlinarith [sq_nonneg (3 - t)]

theorem a_lower_of_one_le {t : ℝ} (h : 1 ≤ t) : 1 / 8 ≤ a t := by
  unfold a
  split_ifs with h₂ h₃
  · linarith
  · have hp : 0 ≤ (t - 2) * (4 - t) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  · norm_num

theorem a_lower_of_two_le {t : ℝ} (h : 2 ≤ t) : 1 / 4 ≤ a t := by
  unfold a
  split_ifs with h₂ h₃
  · linarith
  · have hp : 0 ≤ (t - 2) * (4 - t) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  · norm_num

theorem a_bounds_of_one_le {t : ℝ} (h : 1 ≤ t) : 1 / 8 ≤ a t ∧ a t ≤ 5 / 16 :=
  ⟨a_lower_of_one_le h, a_le_five_sixteenths t⟩

theorem aDeriv_nonneg (t : ℝ) : 0 ≤ aDeriv t := by
  unfold aDeriv
  split_ifs <;> linarith

theorem aDeriv_le (t : ℝ) : aDeriv t ≤ 1 / 8 := by
  unfold aDeriv
  split_ifs <;> linarith

theorem thetaDeriv_nonneg (t : ℝ) : 0 ≤ thetaDeriv t := by
  unfold thetaDeriv
  split_ifs <;> linarith

theorem thetaDeriv_le (t : ℝ) : thetaDeriv t ≤ 1 := by
  unfold thetaDeriv
  split_ifs <;> linarith

theorem theta_nonneg (t : ℝ) : 0 ≤ theta t := by
  unfold theta
  split_ifs <;> nlinarith [sq_nonneg (t - 1)]

/-- The ordered difference estimate also records monotonicity. -/
theorem a_sub_bounds {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ a y - a x ∧ a y - a x ≤ (y - x) / 8 := by
  by_cases hx₂ : x ≤ 2
  · by_cases hy₂ : y ≤ 2
    · rw [a_of_le_two hx₂, a_of_le_two hy₂]
      constructor <;> linarith
    · by_cases hy₃ : y < 3
      · rw [a_of_le_two hx₂, a_of_two_lt_of_lt_three (lt_of_not_ge hy₂) hy₃]
        have hp : 0 ≤ (y - 2) * (4 - y) := mul_nonneg (by linarith) (by linarith)
        constructor <;> nlinarith [sq_nonneg (y - 2)]
      · rw [a_of_le_two hx₂, a_of_three_le (le_of_not_gt hy₃)]
        constructor <;> linarith
  · by_cases hx₃ : x < 3
    · by_cases hy₃ : y < 3
      · rw [a_of_two_lt_of_lt_three (lt_of_not_ge hx₂) hx₃,
            a_of_two_lt_of_lt_three (by linarith) hy₃]
        have hp : 0 ≤ (y - x) * (6 - x - y) :=
          mul_nonneg (sub_nonneg.mpr hxy) (by linarith)
        have hq : 0 ≤ (y - x) * (x + y - 4) :=
          mul_nonneg (sub_nonneg.mpr hxy) (by linarith)
        constructor <;> nlinarith
      · rw [a_of_two_lt_of_lt_three (lt_of_not_ge hx₂) hx₃,
            a_of_three_le (le_of_not_gt hy₃)]
        have hp : 0 ≤ (3 - x) * (x - 1) := mul_nonneg (by linarith) (by linarith)
        constructor <;> nlinarith [sq_nonneg (3 - x)]
    · rw [a_of_three_le (le_of_not_gt hx₃), a_of_three_le (by linarith)]
      constructor <;> linarith

theorem a_monotone : Monotone a := by
  intro x y hxy
  have := (a_sub_bounds hxy).1
  linarith

theorem a_strictMonoOn : StrictMonoOn a (Set.Iic 2) := by
  intro x hx y hy hxy
  rw [a_of_le_two hx, a_of_le_two hy]
  linarith

/-- Ordered differences of the angular profile. -/
theorem theta_sub_bounds {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ theta y - theta x ∧ theta y - theta x ≤ y - x := by
  by_cases hx₁ : x ≤ 1
  · by_cases hy₁ : y ≤ 1
    · rw [theta_of_le_one hx₁, theta_of_le_one hy₁]
      constructor <;> linarith
    · by_cases hy₂ : y < 2
      · rw [theta_of_le_one hx₁, theta_of_one_lt_of_lt_two (lt_of_not_ge hy₁) hy₂]
        have hp : 0 ≤ (y - 1) * (3 - y) := mul_nonneg (by linarith) (by linarith)
        constructor <;> nlinarith [sq_nonneg (y - 1)]
      · rw [theta_of_le_one hx₁, theta_of_two_le (le_of_not_gt hy₂)]
        constructor <;> linarith
  · by_cases hx₂ : x < 2
    · by_cases hy₂ : y < 2
      · rw [theta_of_one_lt_of_lt_two (lt_of_not_ge hx₁) hx₂,
            theta_of_one_lt_of_lt_two (by linarith) hy₂]
        have hp : 0 ≤ (y - x) * (x + y - 2) :=
          mul_nonneg (sub_nonneg.mpr hxy) (by linarith)
        have hq : 0 ≤ (y - x) * (4 - x - y) :=
          mul_nonneg (sub_nonneg.mpr hxy) (by linarith)
        constructor <;> nlinarith
      · rw [theta_of_one_lt_of_lt_two (lt_of_not_ge hx₁) hx₂,
            theta_of_two_le (le_of_not_gt hy₂)]
        have hp : 0 ≤ (2 - x) * x := mul_nonneg (by linarith) (by linarith)
        constructor <;> nlinarith [sq_nonneg (x - 2)]
    · rw [theta_of_two_le (le_of_not_gt hx₂), theta_of_two_le (by linarith)]
      constructor <;> linarith

theorem theta_monotone : Monotone theta := by
  intro x y hxy
  have := (theta_sub_bounds hxy).1
  linarith

theorem theta_strictMonoOn : StrictMonoOn theta (Set.Ici 1) := by
  intro x hx y hy hxy
  by_cases hx₁ : x ≤ 1
  · have hx : x = 1 := le_antisymm hx₁ hx
    subst x
    rw [theta_of_le_one (le_refl 1)]
    by_cases hy₂ : y < 2
    · rw [theta_of_one_lt_of_lt_two hxy hy₂]
      nlinarith [sq_pos_of_pos (show 0 < y - 1 by linarith)]
    · rw [theta_of_two_le (le_of_not_gt hy₂)]
      linarith
  · by_cases hx₂ : x < 2
    · by_cases hy₂ : y < 2
      · rw [theta_of_one_lt_of_lt_two (lt_of_not_ge hx₁) hx₂,
            theta_of_one_lt_of_lt_two (by linarith) hy₂]
        have hp : 0 < (y - x) * (x + y - 2) := mul_pos (by linarith) (by linarith)
        nlinarith
      · rw [theta_of_one_lt_of_lt_two (lt_of_not_ge hx₁) hx₂,
            theta_of_two_le (le_of_not_gt hy₂)]
        have hp : 0 < (2 - x) * x := mul_pos (by linarith) (by linarith)
        nlinarith
    · rw [theta_of_two_le (le_of_not_gt hx₂), theta_of_two_le (by linarith)]
      linarith

private theorem lipschitz_of_ordered_sub {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : Monotone f) (h : ∀ x y, x ≤ y → f y - f x ≤ (K : ℝ) * (y - x)) :
    LipschitzWith K f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases le_total x y with hxy | hyx
  · simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hf hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using h x y hxy
  · simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hf hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)] using h y x hyx

theorem a_lipschitz : LipschitzWith (1 / 8 : ℝ≥0) a := by
  apply lipschitz_of_ordered_sub a_monotone
  intro x y hxy
  norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  linarith [(a_sub_bounds hxy).2]

theorem theta_lipschitz : LipschitzWith 1 theta := by
  apply lipschitz_of_ordered_sub theta_monotone
  intro x y hxy
  simpa using (theta_sub_bounds hxy).2

theorem aDeriv_eq_clip (t : ℝ) : aDeriv t = min (max (3 - t) 0) 1 / 8 := by
  unfold aDeriv
  split_ifs with h₂ h₃
  · rw [max_eq_left (by linarith), min_eq_right (by linarith)]
  · rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  · rw [max_eq_right (by linarith)]
    norm_num

theorem thetaDeriv_eq_clip (t : ℝ) : thetaDeriv t = min (max (t - 1) 0) 1 := by
  unfold thetaDeriv
  split_ifs with h₁ h₂
  · rw [max_eq_right (by linarith)]
    norm_num
  · rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  · rw [max_eq_left (by linarith), min_eq_right (by linarith)]

theorem aDeriv_lipschitz : LipschitzWith (1 / 8 : ℝ≥0) aDeriv := by
  have hbase : LipschitzWith 1 (fun t : ℝ => 3 - t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    have he : (3 - x) - (3 - y) = -(x - y) := by ring
    rw [he, abs_neg]
  have hclip := (hbase.max_const 0).min_const 1
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq]
  rw [aDeriv_eq_clip, aDeriv_eq_clip, ← sub_div, abs_div]
  have hc := hclip.dist_le_mul x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hc
  norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
  linarith

theorem thetaDeriv_lipschitz : LipschitzWith 1 thetaDeriv := by
  have hbase : LipschitzWith 1 (fun t : ℝ => t - 1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [Real.dist_eq, sub_sub_sub_cancel_right]
  have he : thetaDeriv = fun t => min (max (t - 1) 0) 1 := funext thetaDeriv_eq_clip
  rw [he]
  exact (hbase.max_const 0).min_const 1

theorem q_eq_b_sub_a (t : ℝ) : q t = b t - a t := by
  unfold q b
  by_cases h : a t ≤ -(1 / 8)
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [min_eq_right (le_of_not_ge h), max_eq_left (by linarith)]
    ring

theorem q_nonpos (t : ℝ) : q t ≤ 0 := neg_nonpos.mpr (le_max_right _ _)

theorem q_abs_le (t : ℝ) : |q t| ≤ 7 / 16 := by
  rw [q, abs_neg, abs_of_nonneg (le_max_right _ _)]
  apply max_le
  · have := a_le_five_sixteenths t
    linarith
  · norm_num

theorem q_eq_zero_of_a_le {t : ℝ} (h : a t ≤ -(1 / 8)) : q t = 0 := by
  rw [q, max_eq_right (by linarith), neg_zero]

theorem q_eq_zero_of_le_neg_one {t : ℝ} (h : t ≤ -1) : q t = 0 := by
  apply q_eq_zero_of_a_le
  rw [a_of_le_two (by linarith)]
  linarith

theorem q_lipschitz : LipschitzWith (1 / 8 : ℝ≥0) q := by
  have hadd : LipschitzWith (1 / 8 : ℝ≥0) (fun t : ℝ => a t + 1 / 8) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, add_sub_add_right_eq_sub] using a_lipschitz.dist_le_mul x y
  have hmax := hadd.max_const 0
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [q, Real.dist_eq, neg_sub_neg, abs_sub_comm] using hmax.dist_le_mul x y

theorem b_le (t : ℝ) : b t ≤ -(1 / 8) := min_le_right _ _

theorem b_lipschitz : LipschitzWith (1 / 8 : ℝ≥0) b :=
  a_lipschitz.min_const (-(1 / 8))

end ThompsonNonamenability.Analytic

end

end OAI
