import OAI.Geometry.HeilbronnTriangle.Definitions

namespace OAI


namespace Problem355

lemma heilbronnM_ge_three : 3 ≤ heilbronnM := by
  have h : Nat.choose (41 + 1) 41 ≤ Nat.choose (4 * 41 - 1) 41 :=
    Nat.choose_le_choose 41 (by norm_num)
  rw [Nat.choose_succ_self_right] at h
  exact le_trans (by norm_num : 3 ≤ 42) h

lemma heilbronnT_pos : 0 < heilbronnT := by
  exact Nat.choose_pos (n := heilbronnM) (k := 3) heilbronnM_ge_three

private def squareAddOne (t : ℕ) : ℕ := t ^ 2 + 1

private lemma squareAddOne_def (t : ℕ) : squareAddOne t = t ^ 2 + 1 := rfl

lemma heilbronnK_eq : heilbronnK = heilbronnT ^ 2 + 1 := by
  with_unfolding_all exact squareAddOne_def heilbronnT

private lemma squareAddOne_ge {t : ℕ} (ht : 0 < t) : 2 ≤ squareAddOne t := by
  unfold squareAddOne
  nlinarith

lemma heilbronnK_ge_two : 2 ≤ heilbronnK := by
  with_unfolding_all exact squareAddOne_ge (t := heilbronnT) heilbronnT_pos

lemma heilbronnK_pos : 0 < heilbronnK :=
  lt_of_lt_of_le (by norm_num : 0 < 2) heilbronnK_ge_two

private noncomputable def exponentOf (k : ℕ) : ℝ := 1 / (100000 * (k : ℝ))

private lemma exponentOf_pos {k : ℕ} (hk : 0 < k) : 0 < exponentOf k := by
  unfold exponentOf
  positivity

private lemma exponentOf_le {k : ℕ} (hk : 2 ≤ k) : exponentOf k ≤ 1 / 200000 := by
  unfold exponentOf
  have h : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

lemma heilbronnExponent_pos : 0 < heilbronnExponent :=
  exponentOf_pos (k := heilbronnK) heilbronnK_pos

lemma heilbronnExponent_le : heilbronnExponent ≤ 1 / 200000 :=
  exponentOf_le (k := heilbronnK) heilbronnK_ge_two

end Problem355

namespace Problem355.Parameters

def threshold (B k : ℕ) : ℕ := B ^ (k - 1) / 2

lemma base_le_previous_power {B k : ℕ} (hB : 1 ≤ B) (hk : 2 ≤ k) :
    B ≤ B ^ (k - 1) := by
  have h : 1 ≤ k - 1 := by omega
  simpa using (pow_le_pow_right' hB h)

lemma threshold_pos {B k : ℕ} (hB : 3 ≤ B) (hk : 2 ≤ k) :
    0 < threshold B k := by
  have h := base_le_previous_power (by omega : 1 ≤ B) hk
  unfold threshold
  omega

lemma previous_power_le_three_threshold {B k : ℕ} (hB : 3 ≤ B) (hk : 2 ≤ k) :
    B ^ (k - 1) ≤ 3 * threshold B k := by
  have h := base_le_previous_power (by omega : 1 ≤ B) hk
  unfold threshold
  omega

lemma twice_threshold_lt_power {B k : ℕ} (hB : 3 ≤ B) (hk : 2 ≤ k) :
    2 * threshold B k < B ^ k := by
  have hm := base_le_previous_power (by omega : 1 ≤ B) hk
  have he : k = (k - 1) + 1 := by omega
  have hpowe : B ^ k = B ^ (k - 1) * B := by nth_rw 1 [he]; rw [pow_succ]
  rw [hpowe]
  unfold threshold
  have hd : 2 * (B ^ (k - 1) / 2) ≤ B ^ (k - 1) := by omega
  have hp : 0 < B ^ (k - 1) := by omega
  nlinarith

lemma power_le_three_base_threshold {B k : ℕ} (hB : 3 ≤ B) (hk : 2 ≤ k) :
    B ^ k ≤ 3 * B * threshold B k := by
  have h := previous_power_le_three_threshold hB hk
  have he : k = (k - 1) + 1 := by omega
  calc
    B ^ k = B ^ (k - 1) * B := by nth_rw 1 [he]; rw [pow_succ]
    _ ≤ (3 * threshold B k) * B := Nat.mul_le_mul_right B h
    _ = 3 * B * threshold B k := by ring

lemma ratio_bound {B k : ℕ} (hB : 3 ≤ B) (hk : 2 ≤ k) :
    ((B ^ k : ℕ) : ℝ) / (threshold B k : ℝ) ≤ 3 * (B : ℝ) := by
  have ht : (0 : ℝ) < (threshold B k : ℝ) := by exact_mod_cast threshold_pos hB hk
  apply (div_le_iff₀ ht).2
  exact_mod_cast power_le_three_base_threshold hB hk

lemma base_polynomial_bound {B r k : ℕ}
    (hB : B ≤ 200 * k ^ 2 * r ^ 30) (hr : 200 * k ^ 2 ≤ r) :
    B ≤ r ^ 31 := by
  calc
    B ≤ 200 * k ^ 2 * r ^ 30 := hB
    _ ≤ r * r ^ 30 := Nat.mul_le_mul_right _ hr
    _ = r ^ 31 := by ring

lemma auxiliary_polynomial_bound {q h : ℕ} (hh : 2 ≤ h)
    (hq : q ≤ 2 * h ^ 100) : q ≤ h ^ 101 := by
  calc
    q ≤ 2 * h ^ 100 := hq
    _ ≤ h * h ^ 100 := Nat.mul_le_mul_right _ hh
    _ = h ^ 101 := by ring

lemma box_polynomial_bound {B r q k : ℕ}
    (hB : B ≤ r ^ 31) (hq : q ≤ (B ^ k) ^ 101) :
    (B ^ k * q) ^ 10 ≤ r ^ (31620 * k) := by
  calc
    (B ^ k * q) ^ 10 ≤ (B ^ k * (B ^ k) ^ 101) ^ 10 := by gcongr
    _ = B ^ (1020 * k) := by ring
    _ ≤ (r ^ 31) ^ (1020 * k) := Nat.pow_le_pow_left hB _
    _ = r ^ (31620 * k) := by rw [← pow_mul]; congr 1; ring

end Problem355.Parameters

end OAI
