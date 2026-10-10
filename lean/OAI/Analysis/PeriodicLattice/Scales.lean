import OAI.Analysis.PeriodicLattice.Basic

namespace OAI

/-! Temporal scales, smooth profile parameters and derivative budgets. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingScales {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace Scales

def width (wordLength n : ℕ) : ℕ := wordLength + 1 + 2 * n

def codeExponent (wordLength n : ℕ) : ℕ := 2 * width wordLength n + 1

def capacity (b wordLength n : ℕ) : ℕ := b ^ codeExponent wordLength n

def exponent (wordLength n : ℕ) : ℕ :=
  (codeExponent wordLength 0 + 10) * 2 ^ (n * (n + 1))

def epsilon (b wordLength n : ℕ) : ℝ := ((b : ℝ) ^ exponent wordLength n)⁻¹

def beta (b wordLength : ℕ) (n : ℕ) : ℝ :=
  letI := fourAtLeastTwo
  if n = 0 then 1 / 4 else epsilon b wordLength n

@[simp] theorem width_succ (L n : ℕ) : width L (n + 1) = width L n + 2 := by
  simp only [width]
  omega

@[simp] theorem codeExponent_zero (L : ℕ) : codeExponent L 0 = 2 * L + 3 := by
  simp [codeExponent, width]
  omega

theorem codeExponent_eq (L n : ℕ) :
    codeExponent L n = codeExponent L 0 + 4 * n := by
  simp only [codeExponent, width]
  omega

@[simp] theorem codeExponent_succ (L n : ℕ) :
    codeExponent L (n + 1) = codeExponent L n + 4 := by
  simp only [codeExponent, width_succ]
  omega

@[simp] theorem exponent_zero (L : ℕ) : exponent L 0 = 2 * L + 13 := by
  simp [exponent]

theorem exponent_pos (L n : ℕ) : 0 < exponent L n := by
  unfold exponent
  positivity

theorem exponent_succ (L n : ℕ) :
    exponent L (n + 1) = 2 ^ (2 * n + 2) * exponent L n := by
  unfold exponent
  have h : (n + 1) * (n + 1 + 1) = (2 * n + 2) + n * (n + 1) := by ring
  rw [h, pow_add]
  ac_rfl

theorem growthFactor_ge_four (n : ℕ) : 4 ≤ 2 ^ (2 * n + 2) := by
  calc
    4 = (2 : ℕ) ^ 2 := by norm_num
    _ ≤ 2 ^ (2 * n + 2) := Nat.pow_le_pow_right (by decide) (by omega)

theorem four_mul_exponent_le (L n : ℕ) :
    4 * exponent L n ≤ exponent L (n + 1) := by
  rw [exponent_succ]
  exact Nat.mul_le_mul_right _ (growthFactor_ge_four n)

theorem exponent_strictMono (L : ℕ) : StrictMono (exponent L) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hp := exponent_pos L n
  have hg := four_mul_exponent_le L n
  omega

theorem exponent_ge_nextCode (L n : ℕ) : codeExponent L (n + 1) ≤ exponent L n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := four_mul_exponent_le L n
    have hp : 3 ≤ codeExponent L (n + 1) := by
      rw [codeExponent_eq, codeExponent_zero]
      omega
    rw [codeExponent_succ]
    omega

theorem codeExponent_le_exponent (L n : ℕ) : codeExponent L n ≤ exponent L n := by
  have := exponent_ge_nextCode L n
  rw [codeExponent_succ] at this
  omega

theorem exponent_gap (L : ℕ) {k n : ℕ} (hkn : k < n) :
    codeExponent L n ≤ exponent L n - exponent L k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hk : k ≤ m := by omega
  have hm := (exponent_strictMono L).monotone hk
  have hg := four_mul_exponent_le L m
  have hc := exponent_ge_nextCode L m
  simp only [Nat.succ_eq_add_one] at *
  omega

theorem capacity_dvd_inverseScale (b L n : ℕ) :
    capacity b L n ∣ b ^ exponent L n := by
  exact pow_dvd_pow b (codeExponent_le_exponent L n)

theorem capacity_dvd_scaleRatio (b L : ℕ) {k n : ℕ} (hkn : k < n) :
    capacity b L n ∣ b ^ (exponent L n - exponent L k) := by
  exact pow_dvd_pow b (exponent_gap L hkn)

theorem index_le_exponent (L n : ℕ) : n ≤ exponent L n := by
  induction n with
  | zero => omega
  | succ n ih =>
    have := exponent_strictMono L (Nat.lt_succ_self n)
    simp only [Nat.succ_eq_add_one] at *
    omega

theorem exponent_ge_thirteen (L n : ℕ) : 13 ≤ exponent L n := by
  have h := (exponent_strictMono L).monotone (Nat.zero_le n)
  simp only [exponent_zero] at h
  omega

theorem epsilon_pos {b : ℕ} (hb : 2 ≤ b) (L n : ℕ) : 0 < epsilon b L n := by
  unfold epsilon
  have : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  positivity

theorem epsilon_le_one {b : ℕ} (hb : 2 ≤ b) (L n : ℕ) : epsilon b L n ≤ 1 := by
  unfold epsilon
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hb')

theorem epsilon_antitone {b : ℕ} (hb : 2 ≤ b) (L : ℕ) :
    StrictAnti (epsilon b L) := by
  intro m n hmn
  unfold epsilon
  have hb' : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hm : (0 : ℝ) < (b : ℝ) ^ exponent L m := by positivity
  have hpow : (b : ℝ) ^ exponent L m < (b : ℝ) ^ exponent L n :=
    pow_lt_pow_right₀ hb' (exponent_strictMono L hmn)
  simpa only [one_div] using one_div_lt_one_div_of_lt hm hpow

theorem plateau_power_bound {b : ℕ} (hb : 2 ≤ b) (L n : ℕ) :
    (capacity b L (n + 1) : ℝ) * epsilon b L (n + 1) ≤
      epsilon b L n ^ (2 ^ (2 * n + 2) - 1) := by
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hA : 1 ≤ 2 ^ (2 * n + 2) := by have := growthFactor_ge_four n; omega
  have hpow : (b : ℝ) ^ codeExponent L (n + 1) ≤ (b : ℝ) ^ exponent L n :=
    pow_le_pow_right₀ hb' (exponent_ge_nextCode L n)
  have hid : (b : ℝ) ^ exponent L (n + 1) =
      (b : ℝ) ^ exponent L n *
        ((b : ℝ) ^ exponent L n) ^ (2 ^ (2 * n + 2) - 1) := by
    rw [← pow_mul, ← pow_add, exponent_succ]
    congr 1
    have ha : 2 ^ (2 * n + 2) - 1 + 1 = 2 ^ (2 * n + 2) := by omega
    nlinarith
  unfold epsilon capacity
  push_cast
  calc
    (b : ℝ) ^ codeExponent L (n + 1) * ((b : ℝ) ^ exponent L (n + 1))⁻¹ ≤
        (b : ℝ) ^ exponent L n * ((b : ℝ) ^ exponent L (n + 1))⁻¹ :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (((b : ℝ) ^ exponent L n)⁻¹) ^ (2 ^ (2 * n + 2) - 1) := by
      rw [hid, mul_inv, inv_pow]
      have hne : (b : ℝ) ^ exponent L n ≠ 0 := by positivity
      field_simp

theorem epsilon_le_small {b : ℕ} (hb : 2 ≤ b) (L n : ℕ) :
    epsilon b L n ≤ 1 / 8192 := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hpow : (8192 : ℝ) ≤ (b : ℝ) ^ exponent L n := by
    calc
      (8192 : ℝ) = (2 : ℝ) ^ 13 := by norm_num
      _ ≤ (2 : ℝ) ^ exponent L n :=
        pow_le_pow_right₀ (by norm_num) (exponent_ge_thirteen L n)
      _ ≤ (b : ℝ) ^ exponent L n := pow_le_pow_left₀ (by norm_num) hb' _
  simpa only [epsilon, one_div] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8192) hpow

theorem epsilon_cube_lt_quarter {b : ℕ} (hb : 2 ≤ b) (L n : ℕ) :
    epsilon b L n ^ 3 < epsilon b L n / 4 := by
  have he := epsilon_pos hb L n
  have hs := epsilon_le_small hb L n
  have hsq : epsilon b L n ^ 2 < 1 / 4 := by nlinarith
  have h := mul_lt_mul_of_pos_right hsq he
  nlinarith

theorem plateau_bound {b : ℕ} (hb : 2 ≤ b) (L n : ℕ) :
    (capacity b L (n + 1) : ℝ) * epsilon b L (n + 1) ≤
        epsilon b L n ^ (2 ^ (2 * n + 2) - 1) ∧
    epsilon b L n ^ (2 ^ (2 * n + 2) - 1) ≤ epsilon b L n ^ 3 ∧
    epsilon b L n ^ 3 < epsilon b L n / 4 := by
  refine ⟨plateau_power_bound hb L n, ?_, epsilon_cube_lt_quarter hb L n⟩
  apply pow_le_pow_of_le_one (epsilon_pos hb L n).le (epsilon_le_one hb L n)
  have := growthFactor_ge_four n
  omega

theorem epsilon_le_geometric {b : ℕ} (hb : 2 ≤ b) (L n : ℕ) :
    epsilon b L n ≤ accuracy n := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hpow : (2 : ℝ) ^ n ≤ (b : ℝ) ^ exponent L n := by
    calc
      (2 : ℝ) ^ n ≤ (2 : ℝ) ^ exponent L n :=
        pow_le_pow_right₀ (by norm_num) (index_le_exponent L n)
      _ ≤ (b : ℝ) ^ exponent L n := pow_le_pow_left₀ (by norm_num) hb' _
  simpa only [epsilon, accuracy, zpow_neg, zpow_natCast, one_div] using
    one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (2 : ℝ) ^ n) hpow

@[simp] theorem beta_zero (b L : ℕ) : beta b L 0 = 1 / 4 := by simp [beta]

@[simp] theorem beta_succ (b L n : ℕ) : beta b L (n + 1) = epsilon b L (n + 1) := by
  simp [beta]

theorem beta_pos {b : ℕ} (hb : 2 ≤ b) (L n : ℕ) : 0 < beta b L n := by
  unfold beta
  split_ifs
  · norm_num
  · exact epsilon_pos hb L n

theorem beta_strictAnti {b : ℕ} (hb : 2 ≤ b) (L : ℕ) : StrictAnti (beta b L) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [beta_succ]
  by_cases hn : n = 0
  · rw [hn, beta_zero]
    have := epsilon_le_small hb L (0 + 1)
    linarith
  · rw [beta, ite_eq_right hn]
    exact epsilon_antitone hb L (Nat.lt_succ_self n)

theorem beta_le_quarter {b : ℕ} (hb : 2 ≤ b) (L n : ℕ) : beta b L n ≤ 1 / 4 := by
  simpa only [beta_zero] using (beta_strictAnti hb L).antitone (Nat.zero_le n)

theorem growthFactor_ge_index (n : ℕ) : n + 4 ≤ 2 ^ (2 * n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h : 2 * (n + 1) + 2 = (2 * n + 2) + 2 := by omega
    rw [h, pow_add]
    norm_num at *
    omega

theorem differentiated_record_bound {b : ℕ} (hb : 2 ≤ b) (L : ℕ)
    {k n : ℕ} (hkn : k ≤ n) :
    (capacity b L (n + 1) : ℝ) * epsilon b L (n + 1) /
      epsilon b L n ^ k ≤ epsilon b L n := by
  apply (div_le_iff₀ (pow_pos (epsilon_pos hb L n) k)).2
  calc
    (capacity b L (n + 1) : ℝ) * epsilon b L (n + 1) ≤
        epsilon b L n ^ (2 ^ (2 * n + 2) - 1) := plateau_power_bound hb L n
    _ ≤ epsilon b L n ^ (k + 1) := by
      apply pow_le_pow_of_le_one (epsilon_pos hb L n).le (epsilon_le_one hb L n)
      have := growthFactor_ge_index n
      omega
    _ = epsilon b L n * epsilon b L n ^ k := by ring

def slotSize (b L k n : ℕ) : ℝ :=
  (if k = 0 then beta b L n else 0) +
    (capacity b L (n + 1) : ℝ) * epsilon b L (n + 1) / epsilon b L n ^ k

theorem slotSize_le {b : ℕ} (hb : 2 ≤ b) (L : ℕ)
    {k n : ℕ} (hn : 1 ≤ n) (hkn : k ≤ n) :
    slotSize b L k n ≤ 2 * epsilon b L n := by
  have hrec := differentiated_record_bound hb L hkn
  have hbeta : beta b L n = epsilon b L n := by simp [beta, show n ≠ 0 by omega]
  unfold slotSize
  split_ifs
  · rw [hbeta]
    linarith
  · have := (epsilon_pos hb L n).le
    linarith

def weightBound (J : ℕ) : ℕ := 2 ^ (J + 3) * J.factorial

theorem polynomial_geometric_bound (J n : ℕ) :
    ((n : ℝ) + 3) ^ J * accuracy n ≤ (weightBound J : ℝ) := by
  have hexp_half : Real.exp (1 / 2) ≤ 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    norm_num at h
    exact h
  have hexp : Real.exp (((n : ℝ) + 3) / 2) ≤ (2 : ℝ) ^ (n + 3) := by
    calc
      Real.exp (((n : ℝ) + 3) / 2) = (Real.exp (1 / 2)) ^ (n + 3) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ ≤ (2 : ℝ) ^ (n + 3) :=
        pow_le_pow_left₀ (Real.exp_pos _).le hexp_half _
  have hfac : (0 : ℝ) < (J.factorial : ℝ) := by positivity
  have h := Real.pow_div_factorial_le_exp (((n : ℝ) + 3) / 2) (by positivity) J
  have hpoly : ((n : ℝ) + 3) ^ J ≤
      (2 : ℝ) ^ J * (J.factorial : ℝ) * (2 : ℝ) ^ (n + 3) := by
    rw [div_pow, div_div] at h
    have h' := (div_le_iff₀ (mul_pos (by positivity) hfac)).1 (h.trans hexp)
    nlinarith
  unfold accuracy weightBound
  rw [zpow_neg, zpow_natCast]
  push_cast
  calc
    ((n : ℝ) + 3) ^ J * ((2 : ℝ) ^ n)⁻¹ ≤
        ((2 : ℝ) ^ J * (J.factorial : ℝ) * (2 : ℝ) ^ (n + 3)) *
          ((2 : ℝ) ^ n)⁻¹ := mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = (2 : ℝ) ^ (J + 3) * (J.factorial : ℝ) := by
      rw [pow_add, pow_add]
      have hne : (2 : ℝ) ^ n ≠ 0 := by positivity
      field_simp

theorem weighted_slotSize_bound {b : ℕ} (hb : 2 ≤ b) (L J : ℕ)
    {k n : ℕ} (hn : 1 ≤ n) (hkn : k ≤ n) {t : ℝ}
    (ht : 0 ≤ t) (htop : t ≤ (n : ℝ) + 2) :
    (1 + t) ^ J * slotSize b L k n ≤ 2 * (weightBound J : ℝ) := by
  have hslot := slotSize_le hb L hn hkn
  have heps : (1 + t) ^ J * epsilon b L n ≤ (weightBound J : ℝ) := by
    calc
      (1 + t) ^ J * epsilon b L n ≤
          ((n : ℝ) + 3) ^ J * accuracy n :=
        mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) J)
          (epsilon_le_geometric hb L n) (epsilon_pos hb L n).le (by positivity)
      _ ≤ (weightBound J : ℝ) := polynomial_geometric_bound J n
  have h := mul_le_mul_of_nonneg_left hslot (by positivity : (0 : ℝ) ≤ (1 + t) ^ J)
  nlinarith

end Scales

end
end PeriodicLattice

end OAI
