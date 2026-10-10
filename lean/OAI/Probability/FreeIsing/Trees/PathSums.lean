import Mathlib

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem summable_path_attenuation (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-a * n)) :=
  Real.summable_pow_mul_exp_neg_nat_mul k ha

theorem pow_le_factorial_mul_choose (n k : ℕ) :
    (n : ℝ) ^ k ≤ (k.factorial : ℝ) * ((n + k).choose k : ℝ) := by
  have h := (Nat.pow_le_choose (α := ℝ) k (n + k))
  have hnk : n + k + 1 - k = n + 1 := by omega
  rw [hnk] at h
  have hk : (0 : ℝ) < k.factorial := by positivity
  have h' : ((n + 1 : ℕ) : ℝ) ^ k ≤
      ((n + k).choose k : ℝ) * (k.factorial : ℝ) := by
    exact (div_le_iff₀ hk).mp h
  calc
    (n : ℝ) ^ k ≤ ((n + 1 : ℕ) : ℝ) ^ k := by gcongr; exact_mod_cast Nat.le_succ n
    _ ≤ (k.factorial : ℝ) * ((n + k).choose k : ℝ) := by simpa [mul_comm] using h'

theorem tsum_path_attenuation_le (k : ℕ) {a : ℝ} (ha : 0 < a) :
    (∑' n : ℕ, (n : ℝ) ^ k * Real.exp (-a * n)) ≤
      (k.factorial : ℝ) / (1 - Real.exp (-a)) ^ (k + 1) := by
  have he : ‖Real.exp (-a)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hsum := (summable_choose_mul_geometric_of_norm_lt_one k he).mul_left
    (k.factorial : ℝ)
  have hle : (∑' n : ℕ, (n : ℝ) ^ k * Real.exp (-a * n)) ≤
      ∑' n : ℕ, (k.factorial : ℝ) * (((n + k).choose k : ℝ) * Real.exp (-a) ^ n) := by
    apply Summable.tsum_le_tsum _ (summable_path_attenuation k ha) hsum
    intro n
    rw [show -a * (n : ℝ) = (n : ℝ) * -a by ring, Real.exp_nat_mul]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right
      (pow_le_factorial_mul_choose n k) (pow_nonneg (Real.exp_nonneg _) n)
  calc
    _ ≤ _ := hle
    _ = (k.factorial : ℝ) / (1 - Real.exp (-a)) ^ (k + 1) := by
      rw [tsum_mul_left, tsum_choose_mul_geometric_of_norm_lt_one k he]
      ring

theorem half_le_one_sub_exp_neg {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    a / 2 ≤ 1 - Real.exp (-a) := by
  have hmul := mul_le_mul_of_nonneg_right (Real.add_one_le_exp a)
    (Real.exp_nonneg (-a))
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul
  by_cases h : Real.exp (-a) ≤ 1 / 2
  · linarith
  · have h' : 1 / 2 ≤ Real.exp (-a) := le_of_not_ge h
    have := mul_le_mul_of_nonneg_left h' ha
    nlinarith

theorem tsum_path_attenuation_small_le (k : ℕ) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    (∑' n : ℕ, (n : ℝ) ^ k * Real.exp (-a * n)) ≤
      (k.factorial : ℝ) * (2 / a) ^ (k + 1) := by
  have hgap := half_le_one_sub_exp_neg ha.le ha1
  have ha2 : 0 < a / 2 := by positivity
  have hgap0 : 0 < 1 - Real.exp (-a) := ha2.trans_le hgap
  have hinv : (1 - Real.exp (-a))⁻¹ ≤ 2 / a := by
    calc
      (1 - Real.exp (-a))⁻¹ ≤ (a / 2)⁻¹ := inv_anti₀ ha2 hgap
      _ = 2 / a := by field_simp
  calc
    _ ≤ (k.factorial : ℝ) / (1 - Real.exp (-a)) ^ (k + 1) :=
      tsum_path_attenuation_le k ha
    _ = (k.factorial : ℝ) * ((1 - Real.exp (-a))⁻¹) ^ (k + 1) := by
      rw [div_eq_mul_inv, inv_pow]
    _ ≤ (k.factorial : ℝ) * (2 / a) ^ (k + 1) := by gcongr

theorem tsum_linear_path_attenuation_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∑' n : ℕ, (n : ℝ) * Real.exp (-a * n)) ≤ 4 / a ^ 2 := by
  simpa only [Nat.factorial_one, Nat.cast_one, pow_one, Nat.reduceAdd, one_mul,
    div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      tsum_path_attenuation_small_le 1 ha ha1

theorem tsum_quadratic_path_attenuation_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∑' n : ℕ, (n : ℝ) ^ 2 * Real.exp (-a * n)) ≤ 16 / a ^ 3 := by
  convert tsum_path_attenuation_small_le 2 ha ha1 using 1
  norm_num
  ring

theorem sqrt_le_path_affine {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    Real.sqrt x ≤ (a * x + 1) / (2 * Real.sqrt a) := by
  have ha' : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsq : (Real.sqrt a * Real.sqrt x) ^ 2 = a * x := by
    rw [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hx]
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt a)).mpr
  nlinarith [sq_nonneg (Real.sqrt a * Real.sqrt x - 1)]

theorem summable_sqrt_path_attenuation {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => Real.sqrt n * Real.exp (-a * n)) := by
  have hn : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-a * n)) := by
    simpa using summable_path_attenuation 1 ha
  have hg : Summable (fun n : ℕ => Real.exp (-a * n)) := by
    simpa using summable_path_attenuation 0 ha
  apply (hn.add hg).of_nonneg_of_le (fun n => by positivity)
  intro n
  have hs : Real.sqrt (n : ℝ) ≤ (n : ℝ) + 1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]
  calc
    _ ≤ ((n : ℝ) + 1) * Real.exp (-a * n) :=
      mul_le_mul_of_nonneg_right hs (Real.exp_nonneg _)
    _ = _ := by ring

theorem tsum_sqrt_path_attenuation_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∑' n : ℕ, Real.sqrt n * Real.exp (-a * n)) ≤ 3 / (a * Real.sqrt a) := by
  have hn : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-a * n)) := by
    simpa using summable_path_attenuation 1 ha
  have hg : Summable (fun n : ℕ => Real.exp (-a * n)) := by
    simpa using summable_path_attenuation 0 ha
  have hsum := ((hn.mul_left a).add hg).div_const (2 * Real.sqrt a)
  have hle : (∑' n : ℕ, Real.sqrt n * Real.exp (-a * n)) ≤
      ∑' n : ℕ, (a * ((n : ℝ) * Real.exp (-a * n)) + Real.exp (-a * n)) /
        (2 * Real.sqrt a) := by
    apply Summable.tsum_le_tsum _ (summable_sqrt_path_attenuation ha) hsum
    intro n
    calc
      _ ≤ ((a * (n : ℝ) + 1) / (2 * Real.sqrt a)) * Real.exp (-a * n) :=
        mul_le_mul_of_nonneg_right (sqrt_le_path_affine ha (Nat.cast_nonneg n))
          (Real.exp_nonneg _)
      _ = _ := by ring
  have hzero : (∑' n : ℕ, Real.exp (-a * n)) ≤ 2 / a := by
    simpa using tsum_path_attenuation_small_le 0 ha ha1
  calc
    _ ≤ _ := hle
    _ = (a * (∑' n : ℕ, (n : ℝ) * Real.exp (-a * n)) +
        (∑' n : ℕ, Real.exp (-a * n))) / (2 * Real.sqrt a) := by
      rw [tsum_div_const, (hn.mul_left a).tsum_add hg, tsum_mul_left]
    _ ≤ (a * (4 / a ^ 2) + 2 / a) / (2 * Real.sqrt a) := by
      gcongr
      exact tsum_linear_path_attenuation_le ha ha1
    _ = 3 / (a * Real.sqrt a) := by
      field_simp
      ring

theorem summable_superexponential_path (k : ℕ) {a q : ℝ}
    (ha : 0 < a) (hq : 1 < q) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-a * q ^ n)) := by
  have hrate : 0 < a * (q - 1) := mul_pos ha (sub_pos.mpr hq)
  apply (summable_path_attenuation k hrate).of_nonneg_of_le (fun n => by positivity)
  intro n
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have h := one_add_mul_sub_le_pow (show -1 ≤ q by linarith) n
  have h' : (n : ℝ) * (q - 1) ≤ q ^ n := by linarith
  nlinarith

theorem summable_superexponential_rpow_path (k : ℕ) {a b γ : ℝ}
    (ha : 0 < a) (hb : 1 < b) (hγ : 0 < γ) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-a * b ^ (γ * n))) := by
  have hb0 : 0 ≤ b := le_trans zero_le_one hb.le
  simp_rw [Real.rpow_mul_natCast hb0]
  exact summable_superexponential_path k ha (Real.one_lt_rpow hb hγ)

theorem exp_neg_le_sq_of_log_cutoff {V K A : ℝ} (hV : 0 < V) (hK : 1 ≤ K)
    (hA : 2 * (1 + Real.log (K / V)) ≤ A) :
    Real.exp (-A) ≤ V ^ 2 := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  rw [Real.log_div hK0.ne' hV.ne'] at hA
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  calc
    Real.exp (-A) ≤ Real.exp (2 * Real.log V) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = V ^ 2 := by rw [two_mul, Real.exp_add, Real.exp_log hV]; ring

theorem superexponential_path_absorption {V K a q : ℝ} {n : ℕ}
    (hV : 0 < V) (hK : 1 ≤ K)
    (hcut : 2 * (1 + Real.log (K / V)) ≤ (a / 2) * q ^ n) :
    Real.exp (-a * q ^ n) ≤ V ^ 2 * Real.exp (-(a / 2) * q ^ n) := by
  have h := exp_neg_le_sq_of_log_cutoff hV hK hcut
  calc
    Real.exp (-a * q ^ n) =
        Real.exp (-((a / 2) * q ^ n)) * Real.exp (-(a / 2) * q ^ n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ V ^ 2 * Real.exp (-(a / 2) * q ^ n) :=
      mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)

end Problem367

end

end OAI
