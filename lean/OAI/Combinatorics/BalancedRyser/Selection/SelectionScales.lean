import OAI.Combinatorics.BalancedRyser.Probability.TailProductBounds

namespace OAI

noncomputable section

namespace Balanced.SelectionScales

def domain (P : ℝ) (q t : ℕ) : ℝ := (1 - P / q) ^ t

def degree (P : ℝ) (q n t : ℕ) : ℝ := domain P q t * (n - t : ℕ) / n

private theorem rate_bounds {P : ℝ} {q : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) :
    0 ≤ P / q ∧ P / q ≤ 1 / 2 := by
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  constructor
  · exact div_nonneg hP hqR.le
  · apply (div_le_iff₀ hqR).2
    linarith

theorem domain_bounds {P : ℝ} {q t : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) (ht : t ≤ 3 * q) :
    Real.exp (-6 * P) ≤ domain P q t ∧ domain P q t ≤ 1 := by
  obtain ⟨hx, hxhalf⟩ := rate_bounds hP hq hPq
  have hbase : 0 < 1 - P / q := by linarith
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have htR : (t : ℝ) ≤ 3 * q := by exact_mod_cast ht
  constructor
  · rw [domain, ← Real.exp_log (pow_pos hbase t)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_pow]
    have hlog := Balanced.TailProduct.neg_log_one_sub_le_twice hx hxhalf
    have hmul := mul_le_mul_of_nonneg_left (show -2 * (P / q) ≤
        Real.log (1 - P / q) by linarith) (Nat.cast_nonneg t)
    have htime := mul_le_mul_of_nonpos_right htR (show -2 * (P / q) ≤ 0 by linarith)
    have heq : (3 * (q : ℝ)) * (-2 * (P / q)) = -6 * P := by
      field_simp
      ring
    rw [heq] at htime
    exact htime.trans hmul
  · exact pow_le_one₀ hbase.le (by linarith) (n := t)

theorem domain_pos {P : ℝ} {q t : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) :
    0 < domain P q t := by
  obtain ⟨_, hx⟩ := rate_bounds hP hq hPq
  exact pow_pos (by linarith) t

theorem degree_bounds {P a : ℝ} {q n t : ℕ}
    (hP : 0 ≤ P) (ha : 0 ≤ a) (hq : 0 < q) (hn : 0 < n)
    (hPq : 2 * P ≤ q) (hnq : n ≤ 3 * q) (htn : t ≤ n)
    (hremain : a * q ≤ (n - t : ℕ)) :
    Real.exp (-6 * P) * a / 3 ≤ degree P q n t ∧ degree P q n t ≤ 1 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnqR : (n : ℝ) ≤ 3 * q := by exact_mod_cast hnq
  have hremn : ((n - t : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n t
  have hratio : a / 3 ≤ (n - t : ℕ) / (n : ℝ) := by
    apply (le_div_iff₀ hnR).2
    have hprod := mul_le_mul_of_nonneg_left hnqR ha
    nlinarith
  have hratio_one : (n - t : ℕ) / (n : ℝ) ≤ 1 := by
    exact (div_le_one hnR).2 hremn
  have hratio_nonneg : 0 ≤ (n - t : ℕ) / (n : ℝ) := by positivity
  obtain ⟨hdr, hdu⟩ := domain_bounds hP hq hPq (htn.trans hnq)
  change Real.exp (-6 * P) * a / 3 ≤ domain P q t * (n - t : ℕ) / n ∧ _
  rw [mul_div_assoc, mul_div_assoc]
  constructor
  · exact mul_le_mul hdr hratio (by positivity) (domain_pos hP hq hPq).le
  · change domain P q t * (n - t : ℕ) / n ≤ 1
    rw [mul_div_assoc]
    calc
      domain P q t * ((n - t : ℕ) / (n : ℝ)) ≤ 1 * 1 :=
        mul_le_mul hdu hratio_one hratio_nonneg (by norm_num)
      _ = 1 := by ring

theorem domain_succ (P : ℝ) (q t : ℕ) :
    domain P q (t + 1) = (1 - P / q) * domain P q t := by
  simp only [domain, pow_succ, mul_comm]

theorem degree_succ {P : ℝ} {q n t : ℕ} (ht : t < n) :
    degree P q n (t + 1) =
      ((1 - P / q) * (1 - 1 / (n - t : ℕ))) * degree P q n t := by
  have htn : t ≤ n := ht.le
  have htn' : t + 1 ≤ n := ht
  have hrem : (n - t : ℕ) ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt ht)
  have hremR : ((n - t : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hrem
  have hstep : ((n - (t + 1) : ℕ) : ℝ) = (n - t : ℕ) - 1 := by
    rw [Nat.cast_sub htn', Nat.cast_sub htn, Nat.cast_add, Nat.cast_one]
    ring
  simp only [degree, domain_succ, hstep]
  field_simp

theorem domain_ratio {P : ℝ} {q t : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) :
    domain P q (t + 1) / domain P q t = 1 - P / q := by
  rw [domain_succ, mul_div_cancel_right₀ _ (domain_pos hP hq hPq).ne']

theorem degree_pos {P : ℝ} {q n t : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) (ht : t < n) :
    0 < degree P q n t := by
  have hs := domain_pos (t := t) hP hq hPq
  have hh : 0 < ((n - t : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt ht)
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_le t |>.trans_lt ht)
  exact div_pos (mul_pos hs hh) hn

theorem degree_ratio {P : ℝ} {q n t : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) (ht : t < n) :
    degree P q n (t + 1) / degree P q n t =
      (1 - P / q) * (1 - 1 / (n - t : ℕ)) := by
  rw [degree_succ ht, mul_div_cancel_right₀ _ (degree_pos hP hq hPq ht).ne']

theorem domain_relative_change {P : ℝ} {q t : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) :
    |1 - domain P q (t + 1) / domain P q t| = P / q := by
  rw [domain_ratio hP hq hPq, sub_sub_cancel]
  exact abs_of_nonneg (rate_bounds hP hq hPq).1

theorem degree_relative_change_le {P a : ℝ} {q n t : ℕ}
    (hP : 0 ≤ P) (ha : 0 < a) (hq : 0 < q) (hPq : 2 * P ≤ q)
    (ht : t < n) (hremain : a * q ≤ (n - t : ℕ)) :
    |1 - degree P q n (t + 1) / degree P q n t| ≤ (P + 1 / a) / q := by
  obtain ⟨hx, hxh⟩ := rate_bounds hP hq hPq
  have hx1 : P / q ≤ 1 := by linarith
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hh : 0 < ((n - t : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt ht)
  have hy : 0 ≤ 1 / ((n - t : ℕ) : ℝ) := by positivity
  have hxy := mul_le_mul_of_nonneg_right hx1 hy
  have hnon : 0 ≤ 1 - (1 - P / q) * (1 - 1 / (n - t : ℕ)) := by
    nlinarith
  have hyle : 1 / ((n - t : ℕ) : ℝ) ≤ (1 / a) / q := by
    rw [div_div]
    exact one_div_le_one_div_of_le (mul_pos ha hqR) hremain
  rw [degree_ratio hP hq hPq ht, abs_of_nonneg hnon]
  calc
    1 - (1 - P / q) * (1 - 1 / (n - t : ℕ)) ≤
        P / q + 1 / (n - t : ℕ) := by nlinarith [mul_nonneg hx hy]
    _ ≤ P / q + (1 / a) / q := by linarith [hyle]
    _ = (P + 1 / a) / q := by ring

end Balanced.SelectionScales

end

end OAI
