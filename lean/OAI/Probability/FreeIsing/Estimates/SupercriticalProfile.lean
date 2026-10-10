import Mathlib

namespace OAI

noncomputable section

namespace Problem367.SupercriticalProfile

def dual (b theta : ℝ) : ℝ := 1 / (b * theta)

def rate (b theta : ℝ) : ℝ := (1 / theta + b * theta) / (b + 1)

def mixture (b theta : ℝ) : ℝ :=
  (rate b theta - theta) / (rate b theta - dual b theta)

def profile (b theta : ℝ) (n : ℕ) : ℝ :=
  theta ^ n - mixture b theta * dual b theta ^ n

lemma dual_pos {b theta : ℝ} (hb : 0 < b) (htheta : 0 < theta) :
    0 < dual b theta := by
  unfold dual
  positivity

lemma dual_lt {b theta : ℝ} (hb : 0 < b) (htheta : 0 < theta)
    (hsc : 1 < b * theta ^ 2) : dual b theta < theta := by
  unfold dual
  apply (div_lt_iff₀ (mul_pos hb htheta)).2
  nlinarith

lemma rate_sub_theta {b theta : ℝ} (hb : 0 < b) (htheta : 0 < theta) :
    rate b theta - theta = (1 - theta ^ 2) / (theta * (b + 1)) := by
  unfold rate
  field_simp
  ring

lemma rate_sub_dual {b theta : ℝ} (hb : 0 < b) (htheta : 0 < theta) :
    rate b theta - dual b theta = (b * theta - dual b theta) / (b + 1) := by
  unfold rate dual
  field_simp
  ring

lemma rate_sub_dual_pos {b theta : ℝ} (hb : 1 < b) (htheta : 0 < theta)
    (hsc : 1 < b * theta ^ 2) : 0 < rate b theta - dual b theta := by
  rw [rate_sub_dual (by linarith) htheta]
  apply div_pos _ (by linarith)
  have hd := dual_lt (by linarith : 0 < b) htheta hsc
  nlinarith [mul_pos (show 0 < b - 1 by linarith) htheta]

lemma mixture_nonneg {b theta : ℝ} (hb : 1 < b) (htheta : 0 < theta)
    (htheta1 : theta ≤ 1) (hsc : 1 < b * theta ^ 2) :
    0 ≤ mixture b theta := by
  unfold mixture
  apply div_nonneg _ (rate_sub_dual_pos hb htheta hsc).le
  rw [rate_sub_theta (by linarith) htheta]
  apply div_nonneg _ (by positivity)
  nlinarith

lemma mixture_lt_one {b theta : ℝ} (hb : 1 < b) (htheta : 0 < theta)
    (hsc : 1 < b * theta ^ 2) : mixture b theta < 1 := by
  unfold mixture
  apply (div_lt_one (rate_sub_dual_pos hb htheta hsc)).2
  have hd := dual_lt (by linarith : 0 < b) htheta hsc
  linarith

lemma profile_zero_pos {b theta : ℝ} (hb : 1 < b) (htheta : 0 < theta)
    (hsc : 1 < b * theta ^ 2) : 0 < profile b theta 0 := by
  simp only [profile, pow_zero, mul_one]
  exact sub_pos.mpr (mixture_lt_one hb htheta hsc)

lemma profile_le_power {b theta : ℝ} (hb : 1 < b) (htheta : 0 < theta)
    (htheta1 : theta ≤ 1) (hsc : 1 < b * theta ^ 2) (n : ℕ) :
    profile b theta n ≤ theta ^ n := by
  unfold profile
  exact sub_le_self _ (mul_nonneg (mixture_nonneg hb htheta htheta1 hsc)
    (pow_nonneg (dual_pos (by linarith) htheta).le n))

lemma profile_nonneg {b theta : ℝ} (hb : 1 < b) (htheta : 0 < theta)
    (hsc : 1 < b * theta ^ 2) (n : ℕ) :
    0 ≤ profile b theta n := by
  unfold profile
  apply sub_nonneg.mpr
  have hp : dual b theta ^ n ≤ theta ^ n :=
    pow_le_pow_left₀ (dual_pos (by linarith) htheta).le
      (dual_lt (by linarith) htheta hsc).le n
  calc
    mixture b theta * dual b theta ^ n ≤ 1 * dual b theta ^ n :=
      mul_le_mul_of_nonneg_right (mixture_lt_one hb htheta hsc).le
        (pow_nonneg (dual_pos (by linarith) htheta).le n)
    _ ≤ theta ^ n := by simpa using hp

lemma profile_root {b theta : ℝ} (hb : 1 < b) (htheta : 0 < theta)
    (hsc : 1 < b * theta ^ 2) :
    profile b theta 1 = rate b theta * profile b theta 0 := by
  have hd := ne_of_gt (rate_sub_dual_pos hb htheta hsc)
  simp only [profile, pow_one, pow_zero, mul_one, mixture]
  field_simp
  ring

lemma theta_quadratic {b theta : ℝ} (hb : 0 < b) (htheta : 0 < theta) :
    1 + b * theta ^ 2 = (b + 1) * rate b theta * theta := by
  unfold rate
  field_simp

lemma dual_quadratic {b theta : ℝ} (hb : 0 < b) (htheta : 0 < theta) :
    1 + b * dual b theta ^ 2 = (b + 1) * rate b theta * dual b theta := by
  unfold rate dual
  field_simp
  ring

lemma power_recurrence {a b lambda : ℝ}
    (ha : 1 + b * a ^ 2 = (b + 1) * lambda * a) (n : ℕ) :
    a ^ n + b * a ^ (n + 2) = (b + 1) * lambda * a ^ (n + 1) := by
  calc
    a ^ n + b * a ^ (n + 2) = a ^ n * (1 + b * a ^ 2) := by
      rw [pow_add]
      ring
    _ = a ^ n * ((b + 1) * lambda * a) := by rw [ha]
    _ = (b + 1) * lambda * a ^ (n + 1) := by rw [pow_succ]; ring

lemma profile_recurrence {b theta : ℝ} (hb : 0 < b) (htheta : 0 < theta) (n : ℕ) :
    profile b theta n + b * profile b theta (n + 2) =
      (b + 1) * rate b theta * profile b theta (n + 1) := by
  have ht := power_recurrence (theta_quadratic hb htheta) n
  have hd := power_recurrence (dual_quadratic hb htheta) n
  unfold profile
  linear_combination ht - mixture b theta * hd

lemma rate_gap {b theta : ℝ} (hb : 0 < b) (htheta : 0 < theta) :
    rate b theta - 2 * Real.sqrt b / (b + 1) =
      (Real.sqrt b * theta - 1) ^ 2 / (theta * (b + 1)) := by
  have hrs := Real.sq_sqrt hb.le
  unfold rate
  field_simp
  nlinarith [congrArg (fun r : ℝ => r * theta ^ 2) hrs]

lemma rate_gt_tree_rate {b theta : ℝ} (hb : 0 < b) (htheta : 0 < theta)
    (hsc : 1 < b * theta ^ 2) :
    2 * Real.sqrt b / (b + 1) < rate b theta := by
  have hs : (Real.sqrt b * theta) ^ 2 = b * theta ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hb.le]
  have hst : 1 < Real.sqrt b * theta := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg b) htheta.le]
  have hp : 0 < (Real.sqrt b * theta - 1) ^ 2 :=
    sq_pos_of_pos (by linarith)
  have hg := rate_gap hb htheta
  have hq : 0 < (Real.sqrt b * theta - 1) ^ 2 / (theta * (b + 1)) :=
    div_pos hp (by positivity)
  linarith

end Problem367.SupercriticalProfile

end

end OAI
